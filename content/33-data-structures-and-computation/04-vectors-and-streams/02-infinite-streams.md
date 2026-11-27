---
title: Infinite streams
kind: theory
modules:
  - Mathlib.Data.Stream.Defs
  - Mathlib.Data.Stream.Init
explains:
  E3: [Stream', Stream'.cons, Stream'.get, Stream'.tail, Stream'.iterate, Stream'.corec, Stream'.interleave, Stream'.even, Stream'.take, Stream'.ext, Stream'.IsBisimulation, Stream'.get_of_bisim, Stream'.corec_eq, Stream'.iterate_eq, Stream'.even_interleave, Stream'.get_interleave_left, Stream'.take_theorem, Stream'.nats_eq]
  E2: [Stream'.head, Stream'.drop, Stream'.map, Stream'.zip, Stream'.const, Stream'.corec', Stream'.odd, Stream'.nats, Stream'.appendStream', Stream'.cycle, Stream'.head_cons, Stream'.tail_cons, Stream'.get_drop, Stream'.drop_drop, Stream'.map_cons, Stream'.coinduction, Stream'.map_iterate, Stream'.interleave_eq, Stream'.tail_interleave, Stream'.tail_even, Stream'.get_interleave_right, Stream'.interleave_even_odd, Stream'.get_even, Stream'.get_odd, Stream'.length_take, Stream'.take_succ, Stream'.append_take_drop, Stream'.get_nats, Stream'.cycle_eq, Stream'.bisim_simple]
  E1: auto
families: []
requires: [V01.C03, V33.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Infinite streams

### Overview

A stream is an infinite sequence $a_0, a_1, a_2, \ldots$: the natural numbers, the powers of $2$, the outputs of a sensor that never stops. A program never holds a whole stream. It asks for the next element when it needs one. Mathlib models a stream in the simplest way: `Stream' α` is the type of functions `ℕ → α`, and the element at the index $n$ is the value at $n$. With this definition, no coinductive type is necessary, and two streams are equal exactly when they agree at every index.

The interesting part is the method of proof. Many streams are defined by what their head is and what their tail is, for example $\text{nats} = 0 :: \text{map}\ (\cdot + 1)\ \text{nats}$. A proof about such a stream looks at the head and at the tail, again and again. This section turns that idea into the principle of bisimulation, proves it from the extensionality of functions, and applies it to the even and odd parts of a stream and to the interleave of two streams. It also proves the take theorem, which reduces an equality of streams to the equality of all finite prefixes.

### Definitions

**Definition (Stream).** `Stream' α` is `ℕ → α`. The element `s.get n` is $s\, n$. The head `head s` is `s.get 0`, and the tail `tail s` is the stream $i \mapsto s.\text{get}(i + 1)$. More generally, `drop n s` is $i \mapsto s.\text{get}(i + n)$. The stream `cons a s`, with the scoped notation `a :: s` in the namespace `Stream'`, sends $0$ to $a$ and $n + 1$ to $s\, n$. Membership $a \in s$ means $a = s.\text{get}\ n$ for some $n$. The index function is called `get`; the name `nth` of older versions does not exist in this edition.

**Definition (Pointwise operations).** `map f s` is $n \mapsto f(s.\text{get}\ n)$, `zip f s₁ s₂` is $n \mapsto f(s_1.\text{get}\ n)(s_2.\text{get}\ n)$, and `const a` is the stream with the value $a$ everywhere. The stream of natural numbers `nats` is the identity function $n \mapsto n$.

**Definition (Iterate and corecursion).** For $f : \alpha \to \alpha$ and $a : \alpha$, `iterate f a` is defined by recursion on the index: its value at $0$ is $a$, and its value at $n + 1$ is $f$ of its value at $n$. So its value at $n$ is $f^n(a)$. For $f : \alpha \to \beta$ and $g : \alpha \to \alpha$, the corecursive stream `corec f g a` is `map f (iterate g a)`: the state starts at $a$, $g$ moves the state, and $f$ reads an output from each state. The variant `corec' h a`, for $h : \alpha \to \beta \times \alpha$, computes the output and the next state at once.

**Definition (Interleave, even and odd).** The interleave $s_1 \bowtie s_2$ is the corecursive stream with the state $(s_1, s_2)$, the output `head s₁`, and the next state $(s_2, \text{tail } s_1)$. So it alternates: $s_1.\text{get } 0, s_2.\text{get } 0, s_1.\text{get } 1, s_2.\text{get } 1, \ldots$. The stream `even s` is `corec head (tail ∘ tail) s`, the elements at the even indices, and `odd s` is `even (tail s)`.

**Definition (Take and append).** The list `take n s` has the first $n$ elements: `take 0 s = []` and `take (n + 1) s = head s :: take n (tail s)`. For a list $l$, the stream `l ++ₛ s` puts the elements of $l$ in front of $s$. For a nonempty list $l$, `cycle l h` repeats $l$ without end.

**Definition (Bisimulation).** A relation $R$ on `Stream' α` is a bisimulation (`IsBisimulation R`) if $R\, s_1\, s_2$ implies $\text{head } s_1 = \text{head } s_2$ and $R\,(\text{tail } s_1)\,(\text{tail } s_2)$.

### Theorems and proofs

**Lemma (Extensionality and the cons law).** Two streams are equal if they agree at every index (`Stream'.ext`). For every stream $s$, $\text{head } s :: \text{tail } s = s$, and $\text{head}(a :: s) = a$, $\text{tail}(a :: s) = s$.

*Proof.* A stream is a function, so the first claim is function extensionality. For the second, compare at each index. At $0$ both sides give $s\, 0$. At $n + 1$, the left side gives $(\text{tail } s)\, n = s(n + 1)$. The last two equations hold by the definition of `cons`. $\square$

**Proposition (Unfolding equations).** For all $f$, $g$ and $a$:

1. $\text{iterate } f\, a = a :: \text{iterate } f\, (f\, a)$.
2. $\text{corec } f\, g\, a = f\, a :: \text{corec } f\, g\, (g\, a)$.
3. $\text{nats} = 0 :: \text{map}\ (\cdot + 1)\ \text{nats}$.

*Proof.* For the first equation, compare at each index. At $0$ both sides give $a$. At $n + 1$, the left side gives $f^{n+1}(a)$ and the right side gives the value of `iterate f (f a)` at $n$, which is $f^n(f(a))$. The equation $f^{n+1}(a) = f^n(f(a))$ holds by induction on $n$: for $n = 0$ both sides are $f(a)$, and $f^{n+2}(a) = f(f^{n+1}(a)) = f(f^n(f(a))) = f^{n+1}(f(a))$. For the second equation, apply `map f` to the first equation for $g$: the map of a cons is the cons of $f\, a$ and the map of the tail. For the third, at $0$ both sides give $0$, and at $n + 1$ the right side gives $n + 1$, which is the left side. $\square$

The third equation is a definition of `nats` in the form "head and tail". The function definition $n \mapsto n$ is the solution of this equation.

**Theorem (Bisimulation implies equality).** If $R$ is a bisimulation and $R\, s_1\, s_2$, then $s_1 = s_2$.

*Proof.* Show by induction on $n$: for all streams $t_1$, $t_2$ with $R\, t_1\, t_2$, $t_1.\text{get}\ n = t_2.\text{get}\ n$. For $n = 0$, the elements are the heads, and the bisimulation gives $\text{head } t_1 = \text{head } t_2$. For $n + 1$, $t_i.\text{get}(n + 1) = (\text{tail } t_i).\text{get}\ n$. The bisimulation gives $R\,(\text{tail } t_1)\,(\text{tail } t_2)$, and the hypothesis of induction for the tails gives the equality. Apply this to $s_1$ and $s_2$ for every $n$, and use extensionality. $\square$

The proof is short because a stream is a function. In a system with a primitive coinductive type, the same statement is an axiom or a theorem about the final coalgebra. In Mathlib, `Stream'.get_of_bisim` is the induction above, the theorem follows from it, and `Stream'.coinduction` is a variant in which $R$ is the relation "all observations agree".

**Theorem (Interleave).** For all streams $s_1$, $s_2$ and $n : \mathbb{N}$, $(s_1 \bowtie s_2).\text{get}(2n) = s_1.\text{get}\ n$ and $(s_1 \bowtie s_2).\text{get}(2n + 1) = s_2.\text{get}\ n$.

*Proof.* The definition by corecursion and the unfolding equation give $s_1 \bowtie s_2 = \text{head } s_1 :: \text{head } s_2 :: (\text{tail } s_1 \bowtie \text{tail } s_2)$. Induction on $n$ for all $s_1$, $s_2$. For $n = 0$ the two elements are $\text{head } s_1$ and $\text{head } s_2$. For $n + 1$, the index $2(n + 1)$ is $2n + 2$, and two tails remove the two heads: $(s_1 \bowtie s_2).\text{get}(2n + 2) = (\text{tail } s_1 \bowtie \text{tail } s_2).\text{get}(2n)$. The hypothesis of induction gives $(\text{tail } s_1).\text{get}\ n = s_1.\text{get}(n + 1)$. The odd case is the same with $2n + 3$. $\square$

**Theorem (Even part of an interleave).** For all streams, $\text{even}(s_1 \bowtie s_2) = s_1$.

*Proof.* Let $R\, s'\, s$ hold if $s' = \text{even}(s \bowtie s_2)$ for some $s_2$. Then $R\,(\text{even}(s_1 \bowtie s_2))\, s_1$, and it suffices to show that $R$ is a bisimulation. Let $s' = \text{even}(s \bowtie t)$. The head of `even u` is the head of $u$, so $\text{head } s' = \text{head}(s \bowtie t) = \text{head } s$. The tail of `even u` is `even (tail (tail u))`, by the unfolding equation of `corec`. The interleave equation gives $\text{tail}(\text{tail}(s \bowtie t)) = \text{tail } s \bowtie \text{tail } t$. So $\text{tail } s' = \text{even}(\text{tail } s \bowtie \text{tail } t)$, and $R\,(\text{tail } s')\,(\text{tail } s)$ holds with the witness $\text{tail } t$. $\square$

A second proof uses the indices: $\text{even}(u).\text{get}\ n = u.\text{get}(2n)$ (`Stream'.get_even`), and the interleave theorem gives $(s_1 \bowtie s_2).\text{get}(2n) = s_1.\text{get}\ n$. The bisimulation proof is the one in Mathlib, and it is the method that works for the sequences of the next chapter, where no index formula is at hand. In the same way, `Stream'.interleave_even_odd` says $\text{even } s \bowtie \text{odd } s = s$.

**Theorem (Take theorem).** If $\text{take } n\, s_1 = \text{take } n\, s_2$ for every $n$, then $s_1 = s_2$.

*Proof.* First, for all $n$, $s$ and $k < n$, the element at position $k$ of $\text{take } n\, s$ is $s.\text{get}\ k$. Induction on $n$ for all $s$ and $k$: for $n = 0$ there is no $k$. For $n + 1$, the list is $\text{head } s :: \text{take } n\,(\text{tail } s)$. At $k = 0$ the element is $\text{head } s = s.\text{get } 0$. At $k = j + 1$ with $j < n$, the element is the element at $j$ of $\text{take } n\,(\text{tail } s)$, which is $(\text{tail } s).\text{get}\ j = s.\text{get}(j + 1)$ by the hypothesis of induction. Now fix $k$. The lists $\text{take}(k + 1)\, s_1$ and $\text{take}(k + 1)\, s_2$ are equal, so their elements at position $k$ are equal, and these are $s_1.\text{get}\ k$ and $s_2.\text{get}\ k$. Extensionality gives $s_1 = s_2$. $\square$

The converse is trivial, so a stream is determined by its finite prefixes. Also $\text{take } n\, s \mathbin{+\!\!+}_s \text{drop } n\, s = s$ (`Stream'.append_take_drop`), and $\text{take } n\, s$ has the length $n$ (`Stream'.length_take`).

### Examples

**Example (Natural numbers).** The first elements of `nats` are $0, 1, 2, 3$. Its tail is $1, 2, 3, \ldots$, which is `map (· + 1) nats`, as the unfolding equation says. The stream `drop 5 nats` has the value $5 + i$ at $i$, by `get_drop`. The stream `zip (· + ·) nats nats` has the value $2n$ at $n$.

**Example (Powers of two).** The stream `iterate (· * 2) 1` has the elements $1, 2, 4, 8, 16, \ldots$, with the value $2^n$ at $n$. Check the first steps: the value at $0$ is $1$, and each step doubles. The unfolding equation gives `iterate (· * 2) 1 = 1 :: iterate (· * 2) 2`.

**Example (Fibonacci numbers by corecursion).** Let $h(a, b) = (a, (b, a + b))$ and $F = \text{corec'}\ h\ (0, 1)$. The states are $(0, 1), (1, 1), (1, 2), (2, 3), (3, 5), (5, 8)$, and the outputs are their first components. So $\text{take } 6\, F = [0, 1, 1, 2, 3, 5]$. The state holds two numbers, so each element takes one addition.

**Example (Interleave, even and odd).** For $s_1 = \text{nats}$ and $s_2 = \text{const } 0$, the interleave starts $0, 0, 1, 0, 2, 0, 3, 0$. The value at $2n$ is $n$, and the value at $2n + 1$ is $0$, as the theorem says. Its even part is $0, 1, 2, 3, \ldots$, which is `nats` again. The even part of `nats` is $0, 2, 4, 6$, and the odd part is $1, 3, 5, 7$.

```lean
example : Stream'.take 4 (Stream'.even Stream'.nats) = [0, 2, 4, 6] := rfl
```

**Example (A cycle).** The stream `cycle [1, 2] h` is $1, 2, 1, 2, \ldots$. It is a corecursive stream whose state holds the current element, the rest of the current round and the original list; when the rest is empty, the next state starts the list again. The equation `cycle_eq` says that the cycle of $l$ is $l \mathbin{+\!\!+}_s$ the cycle of $l$.

### The library around it

::: mathlib
`Stream'.IsBisimulation` · `Mathlib.Data.Stream.Init`

A relation is a bisimulation if related streams have equal heads and related tails. With `Stream'.get_of_bisim`, related streams agree at every index. The file proves `even_interleave`, `interleave_even_odd`, `bisim_simple` and `map_iterate` with this method.

<?decl Stream'.IsBisimulation?>
:::

::: mathlib
`Stream'.coinduction` · `Mathlib.Data.Stream.Init`

Two streams with equal heads are equal if every observation that agrees on them also agrees on their tails. This form of the principle hides the choice of the relation.

<?decl Stream'.coinduction?>
:::

::: mathlib
`Stream'.take_theorem` · `Mathlib.Data.Stream.Init`

A stream is determined by its finite prefixes. The file has `length_take`, `take_succ`, `take_add` and `append_take_drop`.

<?decl Stream'.take_theorem?>
:::

::: mathlib
`Stream'.corec` · `Mathlib.Data.Stream.Defs`

Corecursion from a state, with `corec_eq` as its unfolding equation and the variants `corec'`, `corecOn` and `unfolds`. The stream `interleave` and the stream `even` are defined with it.

<?decl Stream'.corec?>
:::

::: mathlib
`Stream'.Seq` · `Mathlib.Data.Seq.Defs`

A sequence that may stop: a stream of `Option α` that stays `none` after the first `none`. Chapter 5 of this volume builds it on `Stream'`.

<?decl Stream'.Seq?>
:::

Common errors of a learner: The first error is to search for `Stream'.nth`; the index function in this edition is `Stream'.get`. The second error is to write `a :: s` for a stream without `open Stream'`; the notation is scoped, and without it Lean reads `::` as the cons of lists. The third error is to prove an equality of streams by induction on the streams; a stream is not an inductive type, so the proof uses extensionality with induction on the index, or a bisimulation. The fourth error is to forget the order of the arguments in `drop`: `(drop n s).get i` is `s.get (i + n)`, and `get_drop` states it as `s.get (n + i)`. The fifth error is to confuse `Stream'` with the core type `Std.Stream` of iterators, which is a class and not a type of infinite sequences.

### Exercises

1. (A) Compute the first five elements of `zip (· * ·) nats (const 3)`, of `drop 2 (iterate (· + 3) 1)` and of `odd nats`. Hint: use `get_drop` and the formula $f^n(a)$.
2. (A) Show that $\text{tail}(\text{const } a) = \text{const } a$ and $\text{map } f\,(\text{const } a) = \text{const}(f\, a)$. Hint: compare at each index.
3. (A) Show that $\text{drop } n\,(\text{drop } m\, s) = \text{drop}(m + n)\, s$. Hint: both sides have the value $s.\text{get}(i + n + m)$ at $i$, up to the order of the sum.
4. (B) Prove $\text{map } f\,(\text{iterate } f\, a) = \text{iterate } f\,(f\, a)$ by a bisimulation. Hint: let $R\, s\, t$ hold if $s = \text{map } f\,(\text{iterate } f\, b)$ and $t = \text{iterate } f\,(f\, b)$ for some $b$.
5. (B) Prove $\text{tail}(s_1 \bowtie s_2) = s_2 \bowtie \text{tail } s_1$ from the definition by corecursion. Hint: compute the next state of the corecursion.
6. (B) Prove that $\text{even } s \bowtie \text{odd } s = s$ with the index formulas `get_even`, `get_odd` and the interleave theorem. Hint: split each index into $2n$ or $2n + 1$.
7. (C) Let $F$ be the Fibonacci stream of the examples. Prove that $F.\text{get}(n + 2) = F.\text{get}(n + 1) + F.\text{get}\ n$ for all $n$. Hint: show first that the state after $n$ steps is $(F.\text{get}\ n, F.\text{get}(n + 1))$, by induction on $n$.

### Notes and history

Streams are the standard example of a coinductive type, and bisimulation, which comes from the theory of concurrent processes, is the standard tool to prove their equality. The definition of `Stream'` as a function avoids all of this machinery: a function from $\mathbb{N}$ already has an induction principle on its index. The general final coalgebras of polynomial functors, of which streams are a case, come in Chapter 7.

The Mathlib files are by this author, read from their headers: `Mathlib.Data.Stream.Defs` and `Mathlib.Data.Stream.Init` by Leonardo de Moura.

### Reference

<?reference?>
