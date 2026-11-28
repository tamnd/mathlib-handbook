---
title: The order of Fin n and its intervals
kind: api
modules:
  - Mathlib.Order.Fin.Basic
  - Mathlib.Order.Fin.Clamp
  - Mathlib.Order.Fin.Finset
  - Mathlib.Order.Fin.InsertNth
  - Mathlib.Order.Fin.Prod
  - Mathlib.Order.Fin.SuccAboveOrderIso
  - Mathlib.Order.Fin.Tuple
  - Mathlib.Order.Interval.Set.Fin
  - Mathlib.Order.Interval.Finset.Fin
explains:
  E2: [Fin.top_eq_last, Fin.monotone_iff_le_succ, Fin.coe_orderIso_apply, Fin.orderIsoTriple, Fin.strictMono_insertNth_iff, Fin.consOrderIso, Fin.image_val_Icc, Fin.preimage_rev_Icc, Fin.card_Icc]
  E1: auto
families: []
requires: [V04.C01, V04.C02, V04.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The order of Fin n and its intervals

### Overview

The type `Fin n` has the $n$ natural numbers $0, 1, \dots, n - 1$ as its elements. It is the standard finite linear order of Mathlib: a finite sequence is a function on `Fin n`, a simplex of dimension $n$ has its vertices indexed by `Fin (n + 1)`, and each finite linear order with $n$ elements is isomorphic to `Fin n`. The core library gives `Fin n` the order of the values. This section describes the files of Mathlib that add the order structure on top of that: the lattice and bounded order instances, the order embeddings between different `Fin` types, the order on tuples, and the intervals of `Fin n` as sets and as finite sets.

The files use the linear orders and the bounds of Chapter 1, the order embeddings and isomorphisms of Chapter 2 and the lattices of Chapter 3. The intervals and the locally finite orders are those of Sections 1 and 2 of this chapter.

### The library around it

**Instances and the bounds.** The file `Mathlib.Order.Fin.Basic` gives `Fin.instLinearOrder` and `Fin.instLattice` for each $n$. If $n \ne 0$, the type is nonempty and `Fin.instBoundedOrder` gives it a least and a greatest element; the hypothesis is the class `NeZero n`. The bounds have explicit forms.

$$\bot = 0 \quad (\texttt{Fin.bot\_eq\_zero}), \qquad \top = \operatorname{last} n \quad (\texttt{Fin.top\_eq\_last}).$$

Here `Fin.last n` is the element $n$ of `Fin (n + 1)`, and `Fin.val_top` says that the value of $\top$ in `Fin n` is $n - 1$. Since `Fin n` is a bounded linear order, it is also a Heyting algebra, a co-Heyting algebra and a bi-Heyting algebra, by `Fin.instHeytingAlgebra`, `Fin.instCoheytingAlgebra` and `Fin.instBiheytingAlgebra`; Chapter 3 describes these structures. The order is a well-order (`Fin.Lt.isWellOrder`), and `Fin.compare_eq_compare_val` says that `compare` on `Fin n` is `compare` on the values.

**Monotone maps on `Fin (n + 1)`.** A function on `Fin (n + 1)` is monotone when it increases at each step. This is the property that makes `Fin` useful for sequences.

$$f \text{ monotone} \iff \forall i : \mathrm{Fin}\ n,\ f(\mathrm{castSucc}\ i) \le f(\mathrm{succ}\ i) \qquad (\texttt{Fin.monotone\_iff\_le\_succ}).$$

*Proof.* If $f$ is monotone, then $f(i) \le f(i + 1)$, since $i \le i + 1$. For the converse, take $i \le j$ and prove $f(i) \le f(j)$ by induction on $j - i$. If $j = i$ there is nothing to prove. Otherwise $j = k + 1$ with $i \le k$, and $f(i) \le f(k) \le f(k + 1)$ by the induction hypothesis and the step condition. $\square$

The twins are `Fin.strictMono_iff_lt_succ`, `Fin.antitone_iff_succ_le` and `Fin.strictAnti_iff_succ_lt`. For an order homomorphism `Fin.orderHom_injective_iff` reduces injectivity to $f(i) \ne f(i + 1)$ at each step. The maps of `Fin` itself are monotone: `Fin.strictMono_succ`, `Fin.strictMono_castSucc`, `Fin.strictMono_succAbove`, `Fin.strictMono_addNat` and `Fin.strictMono_natAdd`. The map `Fin.rev`, which sends $i$ to $n - 1 - i$, is antitone (`Fin.rev_anti`), and `Fin.predAbove_right_monotone` and `Fin.predAbove_left_monotone` treat the map `Fin.predAbove`.

**Order embeddings and order isomorphisms.** Each embedding of `Fin` types has a bundled form as an order embedding. The coercion to $\mathbb{N}$ is `Fin.valOrderEmb n`. The maps `Fin.castSuccOrderEmb`, `Fin.succOrderEmb n`, `Fin.castLEOrderEmb h`, `Fin.castAddOrderEmb m`, `Fin.addNatOrderEmb m`, `Fin.natAddOrderEmb n` and `Fin.succAboveOrderEmb p` are the order embedding forms of the maps of the same names. The isomorphisms are `Fin.castOrderIso h` for an equality $n = m$, `Fin.revOrderIso` from the order dual of `Fin n`, and `Fin.orderIsoSubtype` to the subtype of the $i < n$ in $\mathbb{N}$. The image of `Fin.succAboveOrderEmb p` is the complement of $\{p\}$ (`Fin.range_succAboveOrderEmb`), and the file `Mathlib.Order.Fin.SuccAboveOrderIso` makes the isomorphism `Fin.succAboveOrderIso` onto that complement. The file `Mathlib.Order.Fin.Tuple` gives the variant `finSuccAboveOrderIso`, which uses a subtype in place of a set.

An order isomorphism between two `Fin` types does not move the values.

$$e : \mathrm{Fin}\ n \simeq_o \mathrm{Fin}\ m \implies (e(i) : \mathbb{N}) = (i : \mathbb{N}) \qquad (\texttt{Fin.coe\_orderIso\_apply}).$$

*Proof.* The value of $i$ is the number of the elements below $i$: the finite interval `Finset.Iio i` has $i$ elements, by `Fin.card_Iio`. An order isomorphism maps the elements below $i$ bijectively to the elements below $e(i)$. Thus the two numbers are equal, and the value of $e(i)$ is the value of $i$. $\square$

It follows that $n = m$ and that $e$ is the identity up to the cast. The file `Mathlib.Order.Fin.Finset` goes in the other direction and names the order isomorphisms from small `Fin` types onto small sets: `Fin.orderIsoSingleton a` onto $\{a\}$, `Fin.orderIsoPair a b` onto $\{a, b\}$ for $a < b$, and `Fin.orderIsoTriple a b c` onto $\{a, b, c\}$ for $a < b < c$. The values at $0$, $1$ and $2$ are given by lemmas such as `Fin.orderIsoTriple_one`. These isomorphisms appear when a proof must list the elements of a finite chain.

The file `Mathlib.Order.Fin.Clamp` has two lemmas on the clamp function, which sends $k$ to $\min(k, m)$ in `Fin (m + 1)`: `Fin.clamp_monotone` and `Fin.clamp_eq_last`. The file `Mathlib.Order.Fin.Prod` treats the product order on `Fin (p + 1) × Fin (q + 1)`. The lemma `Fin.prod_lt_last_last_iff` says that $i < (p, q)$ exactly when $i_1 + i_2 < p + q$, the twin `Fin.prod_zero_zero_lt_iff` treats $(0, 0) < i$, and `Fin.prod_exists_lt_lt_of_le_of_le` finds an element strictly between two elements whose sums differ by at least $2$.

**Tuples.** A function on `Fin (n + 1)` is the same as its first value and a function on `Fin n`. The file `Mathlib.Order.Fin.Tuple` makes this an order isomorphism for the pointwise order on dependent functions: `Fin.consOrderIso` uses the first value, `Fin.snocOrderIso` uses the last value, and `Fin.insertNthOrderIso p` uses the value at $p$. For two coordinates, `OrderIso.piFinTwoIso` and `OrderIso.finTwoArrowIso` identify the functions on `Fin 2` with pairs. The interval lemma `Fin.insertNth_mem_Icc` splits the condition $q_1 \le x \le q_2$ in the same way.

Other lemmas give the monotonicity of a tuple in terms of its parts. For a prepended value, `Fin.strictMono_cons` says that `Fin.cons a f` is strictly monotone when $a < f(j)$ for each $j$ and $f$ is strictly monotone; `monotone_vecCons` says that a vector in the notation `![a, b, c]` is monotone when its first value is at most the second one and the rest is monotone. For an inserted value the condition has three parts.

$$\operatorname{insertNth} q\, x\, f \text{ strictly monotone} \iff f \text{ strictly monotone} \land \forall i < q,\ f(i) < x \land \forall i \ge q,\ x < f(i) \qquad (\texttt{Fin.strictMono\_insertNth\_iff}).$$

The file `Mathlib.Order.Fin.InsertNth` has the one-sided forms, for example `Fin.insertNth_monotone` and `Fin.strictMono_insertNth_zero`, and `StrictMono.removeNth` says that a value can be removed from a strictly monotone tuple. The lemma `Fin.pi_lex_lt_cons_cons` computes the lexicographic order on tuples: compare the first values, and if they are equal, compare the rest.

**Intervals as sets.** The file `Mathlib.Order.Interval.Set.Fin` computes the images and the preimages of the intervals of Section 1 under the maps of `Fin`. The names follow one pattern: *Fin.image_F_I* and *Fin.preimage_F_I_F*, where *F* is the name of the map and *I* is the kind of interval. For the coercion to $\mathbb{N}$ the result is the interval of the values.

$$\mathrm{val}\,(\,[i, j]\,) = [\,(i : \mathbb{N}),\ (j : \mathbb{N})\,] \qquad (\texttt{Fin.image\_val\_Icc}).$$

The lemma `Fin.preimage_val_Icc_val` is the converse direction, and `Fin.range_val` says that the range of the coercion is `Set.Iio n`. For `Fin.castSucc`, `Fin.succ`, `Fin.castAdd`, `Fin.natAdd` and `Fin.addNat` the image of an interval is again an interval of the same kind, for example `Fin.image_castSucc_Icc` and `Fin.image_succ_Ici`. For `Fin.rev`, which reverses the order, an interval goes to the interval with the reversed bounds.

$$\mathrm{rev}^{-1}(\,[i, j]\,) = [\,\mathrm{rev}\ j,\ \mathrm{rev}\ i\,] \qquad (\texttt{Fin.preimage\_rev\_Icc}).$$

Since `Fin.rev` is an involution, `Fin.image_rev` says that its image and its preimage are equal. The file also gives the unordered intervals, for example `Fin.image_castSucc_uIcc`, and `Fin.range_natAdd_eq_Ici` describes the range of `Fin.natAdd m` as a ray.

**Intervals as finite sets.** The file `Mathlib.Order.Interval.Finset.Fin` gives the instance `Fin.instLocallyFiniteOrder` and its one-sided twins, so that `Finset.Icc a b` makes sense in `Fin n`. The main results count the elements of each interval in terms of the values.

| Lean name | Statement |
|---|---|
| `Fin.card_Icc` | $\#[a, b] = b + 1 - a$ |
| `Fin.card_Ico` | $\#[a, b) = b - a$ |
| `Fin.card_Ioo` | $\#(a, b) = b - a - 1$ |
| `Fin.card_Iic` | $\#(-\infty, b] = b + 1$ |
| `Fin.card_Iio` | $\#(-\infty, b) = b$ |
| `Fin.card_Ici` | $\#[a, \infty) = n - a$ |
| `Fin.card_Ioi` | $\#(a, \infty) = n - 1 - a$ |

The subtraction is the truncated subtraction of $\mathbb{N}$, so for $b < a$ each formula gives $0$. The other lemmas of the file move a finite interval along a map, in three forms: `Finset.map` with an embedding, as in `Fin.map_valEmbedding_Icc`; `Finset.image`, as in `Fin.finsetImage_val_Icc`; and `Finset.attachFin`, which goes from an interval of $\mathbb{N}$ back to `Fin n`, as in `Fin.attachFin_Icc`. Lemmas such as `Fin.Icc_add_one_eq_Ioc` and `Fin.Iio_add_one_eq_Iic` change the kind of an interval; they need a hypothesis such as $a + 1 < n$, because the addition of `Fin n` wraps around.

#### Common errors

1. Using the addition of `Fin n` in an order argument. In `Fin n` the sum $i + 1$ is computed modulo $n$, so `Fin.last n + 1 = 0`, and $i \le i + 1$ is false at the last element. Use `Fin.succ` or `Fin.castSucc` for the next element, or add the hypothesis that the value is less than $n - 1$.
2. Forgetting the `NeZero` instance. The lemmas on $\bot$ and $\top$ need `[NeZero n]`, because `Fin 0` is empty. For `Fin (n + 1)` the instance is found; for `Fin n` with a hypothesis `h : n ≠ 0`, add it with `haveI : NeZero n := ⟨h⟩`.
3. Reading `Fin.card_Icc` as a formula in `Fin n`. The right side is a natural number built from the values `↑a` and `↑b`, not an element of `Fin n`. A rewrite with it leaves coercions in the goal, which `push_cast` can move.

### Exercises

1. (A) Show that the function on `Fin 4` with the values $0, 2, 2, 5$ is monotone, with `Fin.monotone_iff_le_succ` and `decide`.
2. (A) Use `Fin.card_Icc` to show that the interval $[2, 5]$ of `Fin 10` has $4$ elements.
3. (B) Prove that there is no order isomorphism from `Fin 3` to `Fin 4`, with `Fin.coe_orderIso_apply`.
4. (B) Use `Fin.preimage_rev_Icc` to compute the preimage of $[1, 3]$ under `Fin.rev` in `Fin 6`.
5. (B) Let $f : \mathrm{Fin}\ 3 \to \mathbb{N}$ have the values $1, 4, 9$. Find all $x$ for which `Fin.insertNth 1 x f` is strictly monotone, with `Fin.strictMono_insertNth_iff`.
6. (C) Prove that each finite linear order with $n$ elements is order isomorphic to `Fin n`, and that the isomorphism is unique.

### Reference

<?reference?>
