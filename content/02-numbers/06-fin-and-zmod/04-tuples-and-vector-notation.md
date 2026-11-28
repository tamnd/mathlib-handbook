---
title: Tuples and vector notation
kind: api
modules:
  - Mathlib.Data.Fin.Tuple.Basic
  - Mathlib.Data.Fin.VecNotation
  - Mathlib.Data.Fin.Tuple.Take
  - Mathlib.Data.Fin.Tuple.Embedding
  - Mathlib.Data.Fin.Tuple.Finset
  - Mathlib.Data.Fin.Tuple.NatAntidiagonal
  - Mathlib.Data.Fin.Tuple.Sort
  - Mathlib.Data.Fin.Tuple.BubbleSortInduction
  - Mathlib.Data.Fin.Tuple.Curry
  - Mathlib.Data.Fin.Tuple.Reflection
explains:
  E2: [Fin.cons, Fin.cons_self_tail, Fin.insertNth, Fin.removeNth_insertNth, Matrix.vecCons, Finset.Nat.mem_antidiagonalTuple, Tuple.monotone_sort, FinVec.etaExpand_eq, Function.OfArity.curryEquiv]
  E1: auto
families: []
requires: [V02.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Tuples and vector notation

### Overview

An $n$-tuple $(x_0, \dots, x_{n - 1})$ of elements of $\alpha$ is a function $\operatorname{Fin}(n) \to \alpha$. Mathlib uses this encoding everywhere: a vector of $\mathbb{R}^3$ is a function `Fin 3 → ℝ`, a matrix is a function of two indices, and the arguments of a multilinear map form a tuple. A tuple can also be dependent, of type `(i : Fin n) → α i`, with the type of the entry depending on the index.

This section describes the operations on tuples: add or remove an entry at the start, at the end or at a chosen place, join two tuples, and take a first part. It also describes the notation `![a, b, c]`, the finite sets of tuples, the tuples of natural numbers with a given sum, the permutation that sorts a tuple, and the conversion between a function of $n$ arguments and a function of one tuple. Each operation uses a map of the previous section: `Fin.succ` for the start, `Fin.castSucc` for the end, and `Fin.succAbove` for a chosen place.

### The library around it

#### Adding and removing an entry

The module `Mathlib.Data.Fin.Tuple.Basic` has three pairs of operations. Each pair adds one entry to a tuple of length $n$, or removes one entry from a tuple of length $n + 1$.

| Lean name | Statement |
|---|---|
| `Fin.cons x p` | $(x, p_0, \dots, p_{n - 1})$ |
| `Fin.tail q` | $(q_1, \dots, q_n)$, that is $q \circ \operatorname{succ}$ |
| `Fin.snoc p x` | $(p_0, \dots, p_{n - 1}, x)$ |
| `Fin.init q` | $(q_0, \dots, q_{n - 1})$, that is $q \circ \operatorname{castSucc}$ |
| `Fin.insertNth i x p` | $p$ with $x$ put at place $i$ |
| `Fin.removeNth i q` | $q$ with the entry at place $i$ removed, that is $q \circ \operatorname{succAbove}_i$ |

The definition of `Fin.cons` is the core eliminator `Fin.cases`: the value at $0$ is $x$, and the value at $i + 1$ is $p_i$. The definition of `Fin.snoc` uses the last element in the same way, and `Fin.insertNth` is the eliminator `Fin.succAboveCases`. So the three pairs have the same API, and a lemma about one pair usually has a twin for the other two.

**Theorem.** For each tuple $q$ of length $n + 1$, $\operatorname{cons}(q_0, \operatorname{tail}(q)) = q$. For each $x$ and each tuple $p$ of length $n$, $\operatorname{tail}(\operatorname{cons}(x, p)) = p$.

*Proof.* Two functions on $\operatorname{Fin}(n + 1)$ are equal if they agree at $0$ and at each $i + 1$. At $0$, both sides of the first equation give $q_0$. At $i + 1$, the left side gives $\operatorname{tail}(q)_i = q_{i + 1}$. For the second equation, $\operatorname{tail}(\operatorname{cons}(x, p))_i = \operatorname{cons}(x, p)_{i + 1} = p_i$. $\square$

The Lean names are `Fin.cons_self_tail` and `Fin.tail_cons`. The value lemmas `Fin.cons_zero` and `Fin.cons_succ` are simp lemmas. For the end, the lemmas are `Fin.snoc_castSucc`, `Fin.snoc_last`, `Fin.init_snoc` and `Fin.snoc_init_self`. For a chosen place, they are `Fin.insertNth_apply_same`, `Fin.insertNth_apply_succAbove`, `Fin.removeNth_insertNth` and `Fin.insertNth_self_removeNth`. The first two pin down the tuple $\operatorname{insertNth}_i(x, p)$, because the place $i$ and the image of $\operatorname{succAbove}_i$ cover $\operatorname{Fin}(n + 1)$ (`Fin.range_succAbove`). This gives the cancellation $\operatorname{removeNth}_i(\operatorname{insertNth}_i(x, p)) = p$.

The equivalences `Fin.consEquiv`, `Fin.snocEquiv` and `Fin.insertNthEquiv` state that a tuple of length $n + 1$ is the same as one entry and a tuple of length $n$. The special cases at the two ends are `Fin.insertNth_zero'` and `Fin.insertNth_last'`. A tuple of length two is a pair: `piFinTwoEquiv` is the equivalence.

The operations give induction principles on tuples. `Fin.consCases` and `Fin.snocCases` split one tuple. `Fin.consInduction` and `Fin.snocInduction` prove a statement for tuples of each length from the empty tuple. The lemma `Fin.forall_fin_succ_pi` says $(\forall x, P(x)) \iff \forall a\, v, P(\operatorname{cons}(a, v))$, and `Fin.exists_fin_succ_pi` is the form with $\exists$.

The other lemmas follow the operations through the usual constructions. `Fin.cons_update` moves a `Function.update` inside a `Fin.cons`. `Fin.comp_cons` says $g \circ \operatorname{cons}(x, p) = \operatorname{cons}(g(x), g \circ p)$. `Fin.cons_inj` and `Fin.snoc_inj` compare two tuples entry by entry. `Fin.cons_injective_iff` says that $\operatorname{cons}(x, p)$ is injective if and only if $x$ is not in the range of $p$ and $p$ is injective, and `Fin.snoc_injective_iff` is the twin. The order lemma `Fin.cons_le_cons` compares tuples in the product order. `Fin.range_cons` gives $\operatorname{range}(\operatorname{cons}(x, p)) = \{x\} \cup \operatorname{range}(p)$. Reversal turns one end into the other: `Fin.cons_rev` and `Fin.snoc_rev`. The lemma `Fin.removeNth_removeNth_eq_swap` says that two entries can be removed in either order, by the identity on `Fin.succAbove` of the previous section.

#### Joining, repeating and searching

`Fin.append u v` joins a tuple of length $m$ and a tuple of length $n$ into one of length $m + n$. It is the non dependent form of the core eliminator `Fin.addCases`. The values are `Fin.append_left` on `Fin.castAdd` and `Fin.append_right` on `Fin.natAdd`. The rule `Fin.snoc_eq_append` writes `Fin.snoc` as an append of a tuple of length one. A length that is a sum is not always the length that a lemma wants: `Fin.append_assoc` needs a `Fin.cast` because $(m + n) + k$ and $m + (n + k)$ are different terms. `Fin.repeat m a` repeats a tuple $m$ times, with `Fin.repeat_succ`.

`Fin.find p h` is the least index $i$ with $p(i)$, given a proof $h$ that such an index exists. The lemma `Fin.find_spec` says $p(\operatorname{find}\, p\, h)$, `Fin.find_min` says that no smaller index has the property, and `Fin.find_eq_iff` combines the two. The map `Fin.contractNth j op g` combines two neighbour entries: it sends $(g_0, \dots, g_n)$ to $(g_0, \dots, \operatorname{op}(g_j, g_{j + 1}), \dots, g_n)$.

The module `Mathlib.Data.Fin.Tuple.Take` has `Fin.take m h v`, the first $m$ entries of $v$, with `h : m ≤ n`. It is $v \circ \operatorname{castLE}$. The lemma `Fin.take_eq_init` says that the first $n$ entries of a tuple of length $n + 1$ are `Fin.init`, `Fin.take_succ_eq_snoc` adds one entry, `Fin.take_take` composes two takes, and `Fin.take_append_left` takes from a join.

#### Vector notation

The module `Mathlib.Data.Fin.VecNotation` defines the notation `![a, b, c] : Fin 3 → α`. It unfolds to `Matrix.vecCons a (Matrix.vecCons b (Matrix.vecCons c Matrix.vecEmpty))`. The function `Matrix.vecCons` is the non dependent form of `Fin.cons`, and `Matrix.vecEmpty` is the tuple of length zero, written `![]`. A nested vector is a matrix: `![![1, 2], ![3, 4]] : Fin 2 → Fin 2 → ℕ`. The prefix `Matrix` is in the names because the notation was made for matrices.

| Lean name | Statement |
|---|---|
| `Matrix.cons_val_zero` | $\operatorname{vecCons}(x, u)(0) = x$ |
| `Matrix.cons_val_succ` | $\operatorname{vecCons}(x, u)(i + 1) = u(i)$ |
| `Matrix.cons_val_one` | $\operatorname{vecCons}(x, u)(1) = u(0)$ |
| `Matrix.head_cons` | the head of $\operatorname{vecCons}(x, u)$ is $x$ |
| `Matrix.tail_cons` | the tail of $\operatorname{vecCons}(x, u)$ is $u$ |
| `Matrix.cons_head_tail` | $\operatorname{vecCons}(\operatorname{head}(u), \operatorname{tail}(u)) = u$ |
| `Matrix.empty_eq` | each tuple of length zero is `![]` |
| `Matrix.vecCons_inj` | $\operatorname{vecCons}(x, u) = \operatorname{vecCons}(y, v) \iff x = y \wedge u = v$ |
| `Matrix.range_cons` | $\operatorname{range}(\operatorname{vecCons}(x, u)) = \{x\} \cup \operatorname{range}(u)$ |

The head and the tail are `Matrix.vecHead` and `Matrix.vecTail`. The simp lemmas need one argument of the form `Matrix.vecCons _ _`, so simp computes `![a, b, c] 2 = c` but does not rewrite an unknown tuple. For an index that is a numeral, the simproc `Matrix.cons_val` does the computation in one step. The lemmas `Matrix.Fin.cons_vecCons` and `Matrix.Fin.snoc_vecCons` connect the notation with `Fin.cons` and `Fin.snoc`. `Matrix.vecAppend`, `Matrix.vecAlt0` and `Matrix.vecAlt1` join two vectors and take the entries at even and odd places. The lemma `Matrix.injective_pair_iff_ne` says that `![x, y]` is injective if and only if $x \neq y$.

#### Embeddings and finite sets of tuples

The module `Mathlib.Data.Fin.Tuple.Embedding` lifts the operations to injective tuples, the embeddings `Fin n ↪ α`. `Fin.Embedding.cons` and `Fin.Embedding.snoc` add an entry $a$ with a proof that $a$ is not in the range, `Fin.Embedding.tail` and `Fin.Embedding.init` remove one, and `Fin.Embedding.append` joins two embeddings with disjoint ranges. An embedding of `Fin 2` is a pair of distinct elements: `Function.Embedding.twoEmbeddingEquiv` is the equivalence, and `Function.Embedding.embFinTwo` builds the embedding from a proof of $a \neq b$.

The module `Mathlib.Data.Fin.Tuple.Finset` describes the finite set `Fintype.piFinset s` of tuples $f$ with $f_i \in s_i$ for each $i$. The lemma `Fin.mem_piFinset_iff_zero_tail` splits the condition into the first entry and the tail, and `Fin.mem_piFinset_iff_pivot_removeNth` does the same at a chosen place. The lemma `Finset.card_consEquiv_filter_piFinset` counts the tuples whose tail has a property $P$: there are $|s_0|$ choices for the first entry times the number of good tails.

#### Tuples with a given sum

The module `Mathlib.Data.Fin.Tuple.NatAntidiagonal` defines `Finset.Nat.antidiagonalTuple k n`, the set of tuples $x : \operatorname{Fin}(k) \to \mathbb{N}$ with $\sum_i x_i = n$. There are list and multiset forms, `List.Nat.antidiagonalTuple` and `Multiset.Nat.antidiagonalTuple`. For $k = 2$ it is the antidiagonal $\{(a, b) : a + b = n\}$, with `Finset.Nat.antidiagonalTuple_two`.

**Theorem.** $x \in \operatorname{antidiagonalTuple}(k, n)$ if and only if $\sum_i x_i = n$.

*Proof.* The list is defined by recursion on $k$. For $k = 0$ it is the empty tuple when $n = 0$ and empty otherwise, and the empty sum is $0$. For $k + 1$, the list holds the tuples $\operatorname{cons}(a, y)$ with $a + b = n$ and $y \in \operatorname{antidiagonalTuple}(k, b)$. Write $x = \operatorname{cons}(x_0, \operatorname{tail}(x))$. By induction, $x$ is in the list if and only if $\sum_i \operatorname{tail}(x)_i = n - x_0$ with $x_0 \leq n$, that is, $x_0 + \sum_i \operatorname{tail}(x)_i = n$. $\square$

The Lean form is `Finset.Nat.mem_antidiagonalTuple`. The list has no repeated entries (`List.Nat.nodup_antidiagonalTuple`), and it is sorted in the lexicographic order (`List.Nat.antidiagonalTuple_pairwise_pi_lex`). The equivalence `Finset.Nat.sigmaAntidiagonalTupleEquivTuple` says that the sets for all $n$ together hold each tuple once.

#### Sorting a tuple

The module `Mathlib.Data.Fin.Tuple.Sort` sorts a tuple $f : \operatorname{Fin}(n) \to \alpha$ in a linear order. The permutation `Tuple.sort f` is a permutation $\sigma$ of $\operatorname{Fin}(n)$ such that $f \circ \sigma$ is increasing.

**Theorem.** For each $f$, the tuple $f \circ \operatorname{sort}(f)$ is monotone.

*Proof sketch.* The set $G = \{(f(i), i)\}$, `Tuple.graph f`, has $n$ elements, ordered lexicographically: first by the value, then by the index. There is a unique order isomorphism $e : \operatorname{Fin}(n) \to G$, `Tuple.graphEquiv₂`. Let $\sigma(k)$ be the second coordinate of $e(k)$. Then $f(\sigma(k))$ is the first coordinate of $e(k)$. The first coordinate is monotone in the lexicographic order, and $e$ is monotone. So $f \circ \sigma$ is monotone. $\square$

This is `Tuple.monotone_sort`. The sort is stable: two indices with the same value keep their order (`Tuple.isStable_sort`). The lemma `Tuple.unique_monotone` says that each monotone rearrangement $f \circ \tau$ is equal to $f \circ \operatorname{sort}(f)$, and `Tuple.sort_eq_refl_iff_monotone` says that the sort is the identity exactly for a monotone tuple. The decreasing form is `Tuple.sortDesc`, with `Tuple.antitone_sortDesc` and `Tuple.comp_sort_comp_rev_eq_comp_sortDesc`: the decreasing sort is the increasing sort followed by `Fin.rev`.

The module `Mathlib.Data.Fin.Tuple.BubbleSortInduction` gives an induction principle for sorting. Let $P$ be a property of tuples with $P(f)$. Suppose that $P(g)$ implies $P(g \circ (i\ j))$ whenever $i < j$ and $g(j) < g(i)$. Then $P(f \circ \operatorname{sort}(f))$. This is `Tuple.bubble_sort_induction`. It proves, for example, that a sum or a product of the entries does not change under the sort.

#### Currying and proofs by computation

The module `Mathlib.Data.Fin.Tuple.Curry` converts between a function of $n$ arguments, $f\, a_1 \cdots a_n$, and a function of one tuple, $f'(![a_1, \dots, a_n])$. The type `Function.OfArity α β n` is $\alpha \to \cdots \to \alpha \to \beta$ with $n$ arrows. `Function.OfArity.curry` and `Function.OfArity.uncurry` are the two conversions, and `Function.OfArity.curryEquiv` states that they are inverse. The proof is an induction on $n$: the curry of $f$ applied to $a$ is the curry of $f \circ \operatorname{cons}(a)$, and `Fin.cons_self_tail` closes the step. The dependent forms are `Function.FromTypes.curry` and `Function.FromTypes.uncurry`, where the type of the $i$-th argument depends on $i$. For $n = 2$ the conversions are the usual curry and uncurry of a function on pairs, by `Function.OfArity.uncurry_two_eq_uncurry`.

The module `Mathlib.Data.Fin.Tuple.Reflection` gives forms of the usual operations that compute by definition on `![...]`. For example, `FinVec.etaExpand v` reduces to `![v 0, v 1]` for a tuple of length two, and `FinVec.etaExpand_eq` says that it equals $v$. So `(FinVec.etaExpand_eq v).symm` proves $v = ![v_0, v_1]$ with no case analysis. In the same way, `FinVec.forall_iff` turns $\forall v, P(v)$ into $\forall a_0\, a_1, P(![a_0, a_1])$, and `FinVec.sum_eq` turns $\sum_i a_i$ into $a_0 + a_1 + a_2$ for a tuple of length three. The simprocs `Fin.sum_univ_ofNat` and `Fin.prod_univ_ofNat` expand a sum or a product over `Fin n` when $n$ is a numeral.

#### Common errors

1. `Fin.cons` and `Matrix.vecCons` give the same function, but simp lemmas for one do not fire on the other. Rewrite with `Matrix.Fin.cons_vecCons` or state the goal in one form.
2. The tuple `Fin.snoc p x` has length `n + 1`, and `Fin.append u v` has length `m + n`. A tuple of length `1 + n` or `(m + n) + k` needs `Fin.cast` to match, so state lemmas in the length that the definition gives.
3. A dependent tuple `(i : Fin (n + 1)) → α i` gives `Fin.tail q : (i : Fin n) → α i.succ`. The type of an entry changes with the index, so `Fin.cons_succ` is stated with the dependent type, and `simp` can fail to see that two types agree.

### Exercises

1. (A) Compute `Fin.insertNth 1 7 ![1, 2, 3]` and `Fin.removeNth 2 ![4, 5, 6, 7]`.
2. (A) Show that $\operatorname{init}(\operatorname{cons}(x, p)) = \operatorname{cons}(x, \operatorname{init}(p))$ for a tuple $p$ of length $n + 1$.
3. (B) Show that $|\operatorname{antidiagonalTuple}(3, n)| = \binom{n + 2}{2}$ by counting the first entry.
4. (B) Use `Tuple.bubble_sort_induction` to show that $\sum_i f(\operatorname{sort}(f)(i)) = \sum_i f(i)$.
5. (B) Show that a tuple $f : \operatorname{Fin}(n) \to \alpha$ is injective if and only if $f \circ \operatorname{sort}(f)$ is strictly increasing.
6. (C) Prove that $|\operatorname{antidiagonalTuple}(k + 1, n)| = \binom{n + k}{k}$ for each $k$ and $n$.

### Reference

<?reference?>
