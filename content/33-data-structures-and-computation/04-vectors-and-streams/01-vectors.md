---
title: Vectors
kind: theory
modules:
  - Mathlib.Data.Vector.Defs
  - Mathlib.Data.Vector.Basic
  - Mathlib.Data.Vector.Mem
  - Mathlib.Data.Vector.Snoc
  - Mathlib.Data.Vector.MapLemmas
  - Mathlib.Data.Vector.Zip
  - Mathlib.Data.Vector3
explains:
  E3: [List.Vector, List.Vector.cons, List.Vector.head, List.Vector.tail, List.Vector.get, List.Vector.cons_head_tail, List.Vector.ext, List.Vector.inductionOn, List.Vector.ofFn, List.Vector.get_ofFn, Equiv.vectorEquivFin, List.Vector.mapAccumr, List.Vector.snoc, List.Vector.mapAccumr_snoc, List.Vector.mapAccumr_bisim, List.Vector.mem_iff_get, List.Vector.zipWith_get, Vector3]
  E2: [List.Vector.nil, List.Vector.toList, List.Vector.map, List.Vector.map₂, List.Vector.replicate, List.Vector.mapAccumr₂, List.Vector.head_cons, List.Vector.tail_cons, List.Vector.toList_injective, List.Vector.ofFn_get, List.Vector.get_zero, List.Vector.get_cons_succ, List.Vector.get_map, List.Vector.mapAccumr_cons, List.Vector.reverse, List.Vector.reverse_cons, List.Vector.revInductionOn, List.Vector.mapAccumr_eq_map, List.Vector.mapAccumr_mapAccumr, List.Vector.mem_cons_iff, List.Vector.get_mem, List.Vector.zipWith, List.Vector.prod_mul_prod_eq_prod_zipWith, Vector3.nil, Vector3.cons, Vector3.cons_fz, Vector3.cons_fs, Vector3.append, Vector3.append_cons, Vector3.consElim]
  E1: auto
families: []
requires: [V01.C02, V01.C03, V03.C02, V33.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Vectors

### Overview

A program that adds two numbers of $8$ bits needs two inputs of length $8$ and gives an output of length $8$. With lists, the length is a fact that each user must prove again. With vectors, the length is part of the type: a term of `List.Vector α n` is a list of length exactly $n$, and a function of type `List.Vector α n → List.Vector β n` keeps the length by its type alone. The head of a vector of type `List.Vector α (n + 1)` needs no default value, and the index of `get` is a term of `Fin n`, so no index is out of range.

Mathlib defines a vector as a subtype of lists. This choice keeps all the lemmas on lists available: a statement on vectors often reduces to the same statement on `toList`. This section defines the operations, proves the induction principles and the equivalence with `Fin n → α`, studies the maps with an accumulator, and compares the subtype with the second model `Vector3`, in which a vector is a function on `Fin2 n`. The name `List.Vector` is different from the root type `Vector` of the core library, which is an array of fixed size.

### Definitions

**Definition (Vector).** For a type $\alpha$ and $n : \mathbb{N}$, `List.Vector α n` is the subtype `{l : List α // l.length = n}`. The function `toList` returns the list. The empty vector `nil` has the type `List.Vector α 0`. For $a : \alpha$ and $v$ of length $n$, the vector `a ::ᵥ v` (the function `cons`) has the list $a :: v.\text{toList}$ and the length $n + 1$.

**Definition (Access).** The head `head : List.Vector α (n + 1) → α` returns the first element. The type rules out the empty vector, so no default value is necessary. The tail `tail : List.Vector α n → List.Vector α (n - 1)` drops the first element, and it sends `nil` to `nil`. The element `v.get i` at the index $i : \text{Fin } n$ is the element of the list at position $i$.

**Definition (Construction).** The vector `replicate n a` has $n$ copies of $a$. For $f : \text{Fin } n \to \alpha$, the vector `ofFn f` is defined by recursion on $n$: `ofFn f = nil` for $n = 0$, and `ofFn f = f 0 ::ᵥ ofFn (fun i => f i.succ)` for $n + 1$. The vector `v.map f` applies $f$ to each element, and `map₂ f v w` and `zipWith f v w` combine two vectors of the same length element by element. The append of $v$ of length $n$ and $w$ of length $m$ has the length $n + m$. The vector `v.snoc x` is `v ++ x ::ᵥ nil`, of length $n + 1$, and `reverse` reverses the list.

**Definition (Map with an accumulator).** For $f : \alpha \to \sigma \to \sigma \times \beta$, the function `mapAccumr f v s` returns a pair of a final state and a vector of outputs. It works from the right end. On the list, $$\operatorname{mapAccumr} f\, [\,]\, s = (s, [\,]), \qquad \operatorname{mapAccumr} f\, (y :: ys)\, s = (z.1, z.2 :: r.2),$$ where $r = \operatorname{mapAccumr} f\, ys\, s$ and $z = f\, y\, r.1$. So the last element meets the initial state first, and the first element meets the state that the rest produced. The function `mapAccumr₂` does the same with two vectors of the same length.

**Definition (Membership).** Mathlib states membership in a vector through its list: $a \in v.\text{toList}$.

**Definition (Vector3).** The type `Vector3 α n` is `Fin2 n → α`, where `Fin2 n` is the inductive type with `fz : Fin2 (n + 1)` and `fs : Fin2 n → Fin2 (n + 1)`. The empty vector is the empty function. The vector `cons a v` sends `fz` to $a$ and `fs i` to $v\, i$.

### Theorems and proofs

**Theorem (Extensionality).** Two vectors $v, w$ of length $n$ are equal if $v.\text{get}\ i = w.\text{get}\ i$ for all $i : \text{Fin } n$. Also, `toList` is injective.

*Proof.* Two terms of a subtype are equal when their values are equal, so `toList` is injective. The lists $v.\text{toList}$ and $w.\text{toList}$ both have length $n$. Two lists of the same length that agree at each position are equal, by induction on the lists: two empty lists are equal, and two nonempty lists that agree at each position have the same head (position $0$) and tails that agree at each position (position $i + 1$). The hypothesis gives agreement at each position $i < n$. $\square$

**Lemma (Head and tail).** For $v$ of length $n + 1$, `head v ::ᵥ tail v = v`. For each $a$ and $v$, `head (a ::ᵥ v) = a` and `tail (a ::ᵥ v) = v`.

*Proof.* The list of $v$ has length $n + 1$, so it is not empty; write it as $a :: l$. Then `head v = a`, the tail has the list $l$, and the cons of the two has the list $a :: l$. The values are equal, so the vectors are equal. The other two equations hold by the definitions. $\square$

**Theorem (Induction on vectors).** Let $C$ be a family of types over all vectors of all lengths. If $C(\text{nil})$ holds, and $C(w)$ implies $C(x ::ᵥ w)$ for all $x$ and $w$, then $C(v)$ holds for every vector $v$.

*Proof.* Induction on the length $n$. For $n = 0$, the list of $v$ has length $0$, so it is empty and $v = \text{nil}$. For $n + 1$, the lemma gives $v = \text{head } v ::ᵥ \text{tail } v$. The tail has length $n$, so the hypothesis of induction gives $C(\text{tail } v)$, and the step gives $C(\text{head } v ::ᵥ \text{tail } v) = C(v)$. $\square$

This is `List.Vector.inductionOn`, and Mathlib makes it the default eliminator for the tactic `induction`. The principle `revInductionOn` builds a vector from the right, with `snoc` in place of `cons`. Its proof applies `inductionOn` to the reverse of the vector, with `reverse_cons`, which turns a cons into a snoc.

**Theorem (Vectors are functions on Fin n).** The maps `get` and `ofFn` are inverse, so `List.Vector α n ≃ (Fin n → α)`.

*Proof.* First, `get (ofFn f) i = f i`, by induction on $n$ for all $f$. For $n = 0$ there is no $i$. For $n + 1$, `ofFn f = f 0 ::ᵥ ofFn g` with $g\, i = f\, i.\text{succ}$. At $i = 0$, the element is $f\, 0$. At $i = j.\text{succ}$, the element is `get (ofFn g) j`, which is $g\, j = f\, j.\text{succ}$ by the hypothesis of induction. By function extensionality, `get (ofFn f) = f`. Second, `ofFn (get v)` and $v$ have the same element at each index by the first step, so they are equal by extensionality. $\square$

In Lean the equivalence is `Equiv.vectorEquivFin α n`. It transports any structure on $\text{Fin } n \to \alpha$ to vectors, for example the cardinality $|\alpha|^n$ of the vectors over a finite type.

**Theorem (The last element first).** For $v$ of length $n$, $x : \alpha$ and $f : \alpha \to \sigma \to \sigma \times \beta$, let $q = f\, x\, s$ and $r = \operatorname{mapAccumr} f\, v\, q.1$. Then $\operatorname{mapAccumr} f\,(v.\text{snoc } x)\, s = (r.1, r.2.\text{snoc } q.2)$.

*Proof.* Induction on $v$ for all $s$. For $v = \text{nil}$, the snoc is $x ::ᵥ \text{nil}$. Its accumulation first computes $\operatorname{mapAccumr} f\, \text{nil}\, s = (s, \text{nil})$ and then $f\, x\, s = q$, so the result is $(q.1, q.2 ::ᵥ \text{nil})$, and the right side is $(q.1, \text{nil.snoc } q.2)$, the same vector. For $a ::ᵥ v$, the snoc is $a ::ᵥ (v.\text{snoc } x)$. The definition computes the accumulation of $v.\text{snoc } x$ from $s$, which is $(r.1, r.2.\text{snoc } q.2)$ by the hypothesis of induction, and then $p = f\, a\, r.1$, with the result $(p.1, p.2 ::ᵥ r.2.\text{snoc } q.2)$. On the right side, the accumulation of $a ::ᵥ v$ from $q.1$ computes $r$ first and then the same $p$, with the result $(p.1, p.2 ::ᵥ r.2)$, and its snoc with $q.2$ is the same vector. $\square$

**Theorem (Bisimulation of accumulators).** Let $f_1 : \alpha \to \sigma_1 \to \sigma_1 \times \beta$ and $f_2 : \alpha \to \sigma_2 \to \sigma_2 \times \beta$, and let $R$ be a relation between the states with $R\, s_1\, s_2$. Assume that for all $a$ and all states with $R\, s\, q$, the new states are related, $R\,(f_1\, a\, s).1\,(f_2\, a\, q).1$, and the outputs are equal, $(f_1\, a\, s).2 = (f_2\, a\, q).2$. Then for every vector $v$, the final states of $\operatorname{mapAccumr} f_1\, v\, s_1$ and $\operatorname{mapAccumr} f_2\, v\, s_2$ are related by $R$, and the output vectors are equal.

*Proof.* Induction on $v$ from the right, with `revInductionOn`, for all related $s_1$ and $s_2$. For `nil`, the final states are $s_1$ and $s_2$ and both outputs are `nil`. For $v.\text{snoc } x$, the previous theorem says that both sides first process $x$, with $f_1\, x\, s_1$ and $f_2\, x\, s_2$. The hypothesis gives related new states and equal outputs $o$. Then both sides process $v$ from the new states, and the hypothesis of induction gives related final states and equal vectors $u$. Both output vectors are $u.\text{snoc } o$. $\square$

The induction from the right matches the order of the computation. An induction with `cons` would meet the first element last, after the states have already changed. Two corollaries in `Mathlib.Data.Vector.MapLemmas` are `mapAccumr_eq_map`, which turns an accumulation whose outputs do not depend on the state into a `map`, and `mapAccumr_mapAccumr`, which fuses two passes into one pass with a pair of states.

**Proposition (Membership by index).** $a \in v.\text{toList}$ if and only if $v.\text{get}\ i = a$ for some $i : \text{Fin } n$.

*Proof.* An element of a list is the element at some position below the length, and the length is $n$. Conversely, the element at a position of the list is a member. $\square$

**Proposition (zipWith by index).** $(\operatorname{zipWith} f\, x\, y).\text{get}\ i = f\,(x.\text{get}\ i)\,(y.\text{get}\ i)$.

*Proof.* The list of `zipWith f x y` is `List.zipWith f x.toList y.toList`. Both lists have length $n$, so the zipped list has length $n$ and its element at position $i$ combines the elements at position $i$, by induction on $i$ and the lists. $\square$

For a commutative monoid this gives `prod_mul_prod_eq_prod_zipWith`: the product of $x$ times the product of $y$ is the product of the pointwise products. For lists the same law needs a hypothesis that the lengths are equal; for vectors the type supplies it.

### Examples

**Example (Access).** Let $v = 3 ::ᵥ 1 ::ᵥ 2 ::ᵥ \text{nil}$, of type `List.Vector ℕ 3`. Then `v.head = 3`, `v.tail` is the vector $[1, 2]$ of type `List.Vector ℕ 2`, and `v.get 2 = 2`. No index is out of range, but numerals wrap around: the term `v.get 3` is well typed because `3 : Fin 3` is the element $0$, so `v.get 3 = 3`. The vector `v.map (· * 10)` is $[30, 10, 20]$, `v.snoc 5` is $[3, 1, 2, 5]$ of length $4$, and `v.reverse` is $[2, 1, 3]$.

**Example (A running sum from the right).** Let $f\, x\, s = (s + x, s + x)$ and $v = [1, 2, 3]$. The computation starts at the right end with the state $0$: the element $3$ gives the state $3$ and the output $3$; the element $2$ gives $5$ and $5$; the element $1$ gives $6$ and $6$. So $\operatorname{mapAccumr} f\, v\, 0 = (6, [6, 5, 3])$. The output at each position is the sum of the suffix from that position.

```lean
example : (List.mapAccumr (fun x s => (s + x, s + x)) [1, 2, 3] 0) = (6, [6, 5, 3]) := rfl
```

**Example (Addition of binary numbers).** Write a number of $3$ bits with the most significant bit first, so the right end is the bit of value $1$. Let $f\, a\, b\, c = ((a + b + c) / 2, (a + b + c) \bmod 2)$ on bits in $\mathbb{N}$, with the carry $c$ as the state. For $x = [0, 1, 1]$, which is $3$, and $y = [0, 0, 1]$, which is $1$, `mapAccumr₂ f x y 0` computes from the right: $1 + 1 + 0 = 2$ gives the bit $0$ and the carry $1$; then $1 + 0 + 1 = 2$ gives $0$ and $1$; then $0 + 0 + 1 = 1$ gives $1$ and $0$. The result is $(0, [1, 0, 0])$, and $[1, 0, 0]$ is $4 = 3 + 1$. The final state is the carry out of the top bit. A carry that goes from right to left is the reason for the direction of `mapAccumr`.

**Example (Vector3).** In `Vector3 ℕ 2`, the vector $[7, 8]$ is the function with `fz ↦ 7` and `fs fz ↦ 8`, by `cons_fz` and `cons_fs`. The append of `Vector3 α m` and `Vector3 α n` has the type `Vector3 α (n + m)`, with the arguments in this order. Addition recurses on its second argument, so $n + 0$ reduces to $n$ and $n + (m + 1)$ reduces to $(n + m) + 1$, and the equations `[] +-+ w = w` and `(a :: v) +-+ w = a :: (v +-+ w)` hold by definition. For `List.Vector`, the append of $v$ of length $0$ and $w$ of length $m$ has the type `List.Vector α (0 + m)`, which is not the type `List.Vector α m` by definition, and a cast is necessary.

### The library around it

::: mathlib
`List.Vector.inductionOn` · `Mathlib.Data.Vector.Basic`

The induction principle with `nil` and `cons`, the default eliminator for vectors. The variants are `inductionOn₂` and `inductionOn₃` for several vectors of the same length, and `casesOn`. The file `Mathlib.Data.Vector.Snoc` adds `revInductionOn` with `snoc`.

<?decl List.Vector.inductionOn?>
:::

::: mathlib
`Equiv.vectorEquivFin` · `Mathlib.Data.Vector.Basic`

The equivalence `List.Vector α n ≃ (Fin n → α)`, built from `get`, `ofFn`, `ofFn_get` and `get_ofFn`.

<?decl Equiv.vectorEquivFin?>
:::

::: mathlib
`List.Vector.mapAccumr_bisim` · `Mathlib.Data.Vector.MapLemmas`

Two accumulations with related states and equal outputs give equal output vectors. The file has the variants `mapAccumr_bisim_tail` and `mapAccumr₂_bisim`, and the fusion lemmas `mapAccumr_mapAccumr` and `mapAccumr_map`.

<?decl List.Vector.mapAccumr_bisim?>
:::

::: mathlib
`List.Vector.mem_iff_get` · `Mathlib.Data.Vector.Mem`

Membership by index. The file has `get_mem`, `mem_cons_iff`, `mem_succ_iff` with the head and the tail, and `head_mem`.

<?decl List.Vector.mem_iff_get?>
:::

::: mathlib
`Vector3` · `Mathlib.Data.Vector3`

Vectors as functions on `Fin2 n`, with `cons`, `nth`, `ofFn`, `head`, `tail`, `append`, `insert` and the eliminators `nilElim` and `consElim`. The theory of Diophantine sets in `Mathlib.NumberTheory.Dioph` uses this type.

<?decl Vector3?>
:::

Common errors of a learner: The first error is to confuse `List.Vector` with the root `Vector`, which is an array type of the core library with another set of lemmas. The second error is to write `v.tail` for a vector of type `List.Vector α (n + 1)` and expect the type `List.Vector α n`; the result has the type `List.Vector α (n + 1 - 1)`, which reduces to it, but a lemma may need `simp` to see this. The third error is to expect `mapAccumr` to work from left to right; it starts at the last element. The fourth error is to prove a statement on vectors of length `n + 0` or `0 + n` and meet a mismatch of types; rewrite the length with an equation and use `List.Vector.congr`. The fifth error is to look for membership `a ∈ v` without `toList`; the lemmas of `Mathlib.Data.Vector.Mem` state it on the list.

### Exercises

1. (A) For $v = [4, 0, 7]$ in `List.Vector ℕ 3`, compute `v.head`, `v.tail`, `v.get 1`, `v.snoc 9`, `v.reverse` and `map₂ (· + ·) v v`. Hint: `map₂` works position by position.
2. (A) Compute $\operatorname{mapAccumr} (\text{fun } x\, s \Rightarrow (s + 1, s \cdot x))\, [5, 5, 5]\, 0$. Hint: the state counts from the right.
3. (A) Show that `List.Vector α 0` has exactly one element. Hint: a list of length $0$ is empty.
4. (B) Prove `(v.map f).get i = f (v.get i)` by the induction principle on vectors. Hint: use `get_cons_succ` in the step and the cases $i = 0$ and $i = j.\text{succ}$.
5. (B) Prove that `(v.snoc x).reverse = x ::ᵥ v.reverse`. Hint: on lists, the reverse of $l \mathbin{+\!\!+} [x]$ is $x :: l.\text{reverse}$.
6. (B) Use the bisimulation theorem to prove: if $f\, a\, s = (s, g\, a)$ for all $a$ and $s$, then the outputs of `mapAccumr f v s` equal `v.map g`. Hint: take $R$ to be the relation that always holds, and use `List.Vector.map_eq_mapAccumr`.
7. (C) Prove that binary addition with `mapAccumr₂` is correct: for bit vectors $x$, $y$ of length $n$ with value $[x]$, and the carry $c$, the result $(c', z)$ satisfies $[z] + 2^n c' = [x] + [y] + c$. Hint: use the induction from the right on both vectors, with `revInductionOn₂`, since the last bit is processed first.

### Notes and history

Lists with a length in their type are a standard example of dependent types; in Lean and in other proof assistants they are often defined as an inductive family indexed by $\mathbb{N}$. Mathlib chooses a subtype of lists instead, so the large library of list lemmas applies at once. The second model `Vector3` keeps a definition by recursion on the length, which helps when the length is a concrete numeral and the terms must reduce. The direction of `mapAccumr` follows the Haskell function `mapAccumR`.

The Mathlib files are by these authors, read from their headers: `Mathlib.Data.Vector.Defs` by Leonardo de Moura, `Mathlib.Data.Vector.Basic` by Mario Carneiro, `Mathlib.Data.Vector.Mem` by Devon Tuma, `Mathlib.Data.Vector.Snoc` and `Mathlib.Data.Vector.MapLemmas` by Alex Keizer, `Mathlib.Data.Vector.Zip` by Kim Morrison, and `Mathlib.Data.Vector3` by Mario Carneiro.

### Reference

<?reference?>
