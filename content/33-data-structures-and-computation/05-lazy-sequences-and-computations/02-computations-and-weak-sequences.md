---
title: Computations and weak sequences
kind: theory
modules:
  - Mathlib.Data.Seq.Computation
  - Mathlib.Data.Seq.Parallel
  - Mathlib.Data.WSeq.Defs
  - Mathlib.Data.WSeq.Basic
  - Mathlib.Data.WSeq.Productive
  - Mathlib.Data.WSeq.Relation
  - Mathlib.Data.Semiquot
explains:
  E3: [Computation, Computation.pure, Computation.think, Computation.thinkN, Computation.empty, Computation.destruct, Computation.Terminates, Computation.Results, Computation.mem_unique, Computation.bind, Computation.results_bind, Computation.Equiv, Computation.parallel, Computation.terminates_parallel, Computation.exists_of_mem_parallel, Stream'.WSeq, Stream'.WSeq.destruct, Stream'.WSeq.join_cons, Stream'.WSeq.Equiv, Stream'.WSeq.think_equiv, Stream'.WSeq.Productive, Semiquot, Semiquot.mem_bind, Semiquot.isPure_univ]
  E2: [Computation.corec, Computation.corec_eq, Computation.runFor, Computation.think_empty, Computation.Mem, Computation.get, Computation.length, Computation.get_mem, Computation.results_thinkN, Computation.results_thinkN_pure, Computation.Results.len_unique, Computation.length_thinkN, Computation.ret_bind, Computation.think_bind, Computation.bind_pure, Computation.bind_assoc, Computation.length_bind, Computation.mem_bind, Computation.monad, Computation.orElse, Computation.ret_orElse, Computation.orElse_pure, Computation.orElse_think, Computation.empty_orElse, Computation.orElse_empty, Computation.not_terminates_empty, Computation.think_equiv, Computation.thinkN_equiv, Computation.bind_congr, Computation.equiv_pure_of_mem, Computation.LiftRel, Computation.lift_eq_iff_equiv, Computation.Promises, Computation.parallel_promises, Computation.mem_parallel, Computation.map_parallel, Computation.parallel_congr_left, Stream'.WSeq.nil, Stream'.WSeq.cons, Stream'.WSeq.think, Stream'.WSeq.head, Stream'.WSeq.tail, "Stream'.WSeq.get?", Stream'.WSeq.toList, Stream'.WSeq.ofSeq, Stream'.WSeq.ofList, Stream'.WSeq.append, Stream'.WSeq.join, Stream'.WSeq.join_think, Stream'.WSeq.map, Stream'.WSeq.ret, Stream'.WSeq.bind, Stream'.WSeq.monad, Stream'.WSeq.length, Stream'.WSeq.IsFinite, Stream'.WSeq.LiftRelO, Stream'.WSeq.LiftRel, Stream'.WSeq.ret_bind, Stream'.WSeq.bind_ret, Stream'.WSeq.bind_assoc, Stream'.WSeq.join_ret, Stream'.WSeq.productive_iff, Stream'.WSeq.productive_ofSeq, Stream'.WSeq.toSeq, Semiquot.pure, Semiquot.map, Semiquot.bind, Semiquot.blur, Semiquot.IsPure, Semiquot.get, Semiquot.univ, Semiquot.instLawfulMonad]
  E1: auto
families: []
requires: [V01.C02, V03.C02, V24.C06, V33.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Computations and weak sequences

### Overview

A total function must give a value for each input. A search, an interpreter or an iterative solver can run for ever. Mathlib gives such programs a type: `Computation α` is a possibly infinite run that either stops with a value of type `α` after finitely many steps or never stops. Each step is a tick of a clock, and the run records only whether it has stopped yet.

A computation is a sequence of the previous section with one change: once a value appears, it stays for ever. This makes the time of the result visible. Two computations with the same result and different times are different elements of the type, but they are equivalent. Computations form a monad, and programs with loops can be written in this monad.

Weak sequences combine the two ideas. A weak sequence can produce elements, can stop, and can spend any finite number of ticks between two elements. Many operations, such as filter, can take unbounded time between outputs, so they live on weak sequences. The laws of weak sequences hold only up to equivalence, so the type is not a lawful monad in Lean. The last part of the section treats semiquotients, a related device for nondeterministic choice.

### Definitions

**Definition (Computation).** A computation over $\alpha$ is a stream $c : \mathbb{N} \to \mathrm{Option}\ \alpha$ such that $c(n) = \mathrm{some}\ a$ implies $c(n + 1) = \mathrm{some}\ a$. The value $c(n)$ is the state after $n$ ticks; Mathlib calls it $\mathrm{runFor}\ c\ n$.

**Definition (Pure, think and empty).** The computation $\mathrm{pure}\ a$ is the constant stream $\mathrm{some}\ a$. For a computation $c$, the computation $\mathrm{think}\ c$ has $\mathrm{none}$ at $0$ and $c(n)$ at $n + 1$. The computation $\mathrm{thinkN}\ c\ n$ applies think $n$ times. The computation $\mathrm{empty}$ is the constant stream $\mathrm{none}$; it satisfies $\mathrm{empty} = \mathrm{think}\ \mathrm{empty}$.

**Definition (Destruct and corecursion).** The function $\mathrm{destruct}\ c$ returns $\mathrm{inl}\ a$ when $c(0) = \mathrm{some}\ a$, and $\mathrm{inr}(\mathrm{tail}\ c)$ when $c(0) = \mathrm{none}$. For a step $f : \beta \to \alpha \oplus \beta$, the computation $\mathrm{corec}\ f\ b$ is $\mathrm{pure}\ a$ when $f(b) = \mathrm{inl}\ a$, and $\mathrm{think}(\mathrm{corec}\ f\ b')$ when $f(b) = \mathrm{inr}\ b'$.

So each computation is $\mathrm{pure}\ a$ or $\mathrm{think}\ c'$, and destruct tells which. In the first case, the stability condition forces all entries to be $\mathrm{some}\ a$.

**Definition (Result, termination and length).** A value $a$ is a result of $c$, written $a \in c$, when $c(n) = \mathrm{some}\ a$ for some $n$. The computation $c$ terminates when it has a result. For a terminating $c$, the length of $c$ is the least $n$ with $c(n) \neq \mathrm{none}$, and the value $\mathrm{get}\ c$ is the entry at that index. The statement $\mathrm{Results}\ c\ a\ n$ says that $a \in c$ and the length of $c$ is $n$.

**Definition (Bind).** For $c : \mathrm{Computation}\ \alpha$ and $f : \alpha \to \mathrm{Computation}\ \beta$, the computation $\mathrm{bind}\ c\ f$ runs $c$ tick by tick. When $c$ gives the value $a$, it continues with $f(a)$ tick by tick. It is a corecursion on the states $\mathrm{Computation}\ \alpha \oplus \mathrm{Computation}\ \beta$. With $\mathrm{pure}$ and $\mathrm{bind}$, computations form a monad.

**Definition (Equivalence).** Two computations $c_1, c_2$ are equivalent, written $c_1 \sim c_2$, when $a \in c_1 \iff a \in c_2$ for each $a$. For a relation $R$, the relation $\mathrm{LiftRel}\ R\ c_1\ c_2$ says that each result of $c_1$ is related to some result of $c_2$, and conversely. A computation $c$ promises $a$ when each result of $c$ equals $a$.

**Definition (Weak sequence).** A weak sequence over $\alpha$ is a sequence over $\mathrm{Option}\ \alpha$. The entry $\mathrm{some}\ a$ is an element, and the entry $\mathrm{none}$ is a tick. The constructors are $\mathrm{nil}$, $\mathrm{cons}\ a\ s$ and $\mathrm{think}\ s$. The function $\mathrm{destruct} : \mathrm{WSeq}\ \alpha \to \mathrm{Computation}(\mathrm{Option}(\alpha \times \mathrm{WSeq}\ \alpha))$ skips ticks until it meets the end or an element.

**Definition (Equivalence of weak sequences).** For a relation $R$, the relation $\mathrm{LiftRel}\ R\ s\ t$ holds when there is a relation $C$ with $C\ s\ t$ such that, for each pair $(s', t')$ in $C$, the destructs of $s'$ and $t'$ are related by $\mathrm{LiftRel}$ of computations with this case condition: both are $\mathrm{none}$, or they are $\mathrm{some}(a, s'')$ and $\mathrm{some}(b, t'')$ with $R\ a\ b$ and $C\ s''\ t''$. Equivalence, written $s \sim^w t$, is $\mathrm{LiftRel}$ of equality.

**Definition (Productive weak sequence).** A weak sequence $s$ is productive when, for each $n$, the computation $\mathrm{get?}\ s\ n$ of its entry at $n$ terminates. So a productive weak sequence never ticks for ever before its next element.

**Definition (Semiquotient).** A semiquotient over $\alpha$ is a set $S \subseteq \alpha$ with a truncated witness, an element of $\mathrm{Trunc}\ S$. The witness proves that $S$ is nonempty, but it gives no way to read off a particular element. Membership $a \in q$ means $a \in S$. A semiquotient is pure when $S$ has at most one element.

### Theorems and proofs

**Lemma (Uniqueness of results).** If $a \in c$ and $b \in c$, then $a = b$.

*Proof.* Take $m$ with $c(m) = \mathrm{some}\ a$ and $n$ with $c(n) = \mathrm{some}\ b$. Suppose $m \leq n$; the other case is symmetric. The stability condition, applied $n - m$ times, gives $c(n) = \mathrm{some}\ a$. So $\mathrm{some}\ a = \mathrm{some}\ b$, and $a = b$. $\square$

**Lemma (Results of think).** If $\mathrm{Results}\ c\ a\ n$, then $\mathrm{Results}(\mathrm{think}\ c)\ a\ (n + 1)$. Also $\mathrm{Results}(\mathrm{pure}\ a)\ a\ 0$, so $\mathrm{Results}(\mathrm{thinkN}(\mathrm{pure}\ a)\ n)\ a\ n$.

*Proof.* The entry of $\mathrm{think}\ c$ at $k + 1$ is $c(k)$, and the entry at $0$ is $\mathrm{none}$. So $\mathrm{think}\ c$ has the result $a$, and its first index with an entry is one more than that of $c$. The computation $\mathrm{pure}\ a$ has the entry $\mathrm{some}\ a$ at $0$, so its length is $0$. The statement for $\mathrm{thinkN}$ follows by induction on $n$. $\square$

**Theorem (Shape of a terminating computation).** If $\mathrm{Results}\ c\ a\ n$, then $c = \mathrm{thinkN}(\mathrm{pure}\ a)\ n$.

*Proof.* Induction on $n$, for all $c$. Split $c$ with destruct. Case $c = \mathrm{pure}\ a'$: the length of $c$ is $0$, so $n = 0$, and $a = a'$ by uniqueness of results; then $c = \mathrm{thinkN}(\mathrm{pure}\ a)\ 0$. Case $c = \mathrm{think}\ c'$: the entry at $0$ is $\mathrm{none}$, so $n \neq 0$; write $n = n' + 1$. The result $a$ of $c$ is a result of $c'$, and the length of $c$ is the length of $c'$ plus one, so $\mathrm{Results}\ c'\ a\ n'$. The induction hypothesis gives $c' = \mathrm{thinkN}(\mathrm{pure}\ a)\ n'$, so $c = \mathrm{think}(\mathrm{thinkN}(\mathrm{pure}\ a)\ n') = \mathrm{thinkN}(\mathrm{pure}\ a)(n' + 1)$. $\square$

**Theorem (Results of a bind).** If $\mathrm{Results}\ c\ a\ m$ and $\mathrm{Results}(f\ a)\ b\ n$, then $\mathrm{Results}(\mathrm{bind}\ c\ f)\ b\ (n + m)$.

*Proof.* Two equations follow from the definition of bind by one step of the corecursion: $\mathrm{bind}(\mathrm{pure}\ a)\ f = f(a)$, and $\mathrm{bind}(\mathrm{think}\ c')\ f = \mathrm{think}(\mathrm{bind}\ c'\ f)$. By the theorem on shapes, $c = \mathrm{thinkN}(\mathrm{pure}\ a)\ m$. The second equation, applied $m$ times, and then the first give $\mathrm{bind}\ c\ f = \mathrm{thinkN}(f\ a)\ m$. Again by the theorem on shapes, $f(a) = \mathrm{thinkN}(\mathrm{pure}\ b)\ n$. So $\mathrm{bind}\ c\ f = \mathrm{thinkN}(\mathrm{pure}\ b)(n + m)$, and the lemma on think gives the claim. $\square$

So the length of a bind is the sum of the two lengths. Mathlib states this as `length (bind s f) = length (f (get s)) + length s`.

**Proposition (Think is invisible up to equivalence).** For each computation $c$, $\mathrm{think}\ c \sim c$.

*Proof.* If $a \in c$ with $c(n) = \mathrm{some}\ a$, then the entry of $\mathrm{think}\ c$ at $n + 1$ is $\mathrm{some}\ a$. If $a \in \mathrm{think}\ c$ with entry $\mathrm{some}\ a$ at $k$, then $k \neq 0$, and $c(k - 1) = \mathrm{some}\ a$. $\square$

**Theorem (Parallel search).** Let $S$ be a weak sequence of computations, and let $\mathrm{parallel}\ S$ be the computation that runs them by diagonal interleaving. If some $c$ in $S$ terminates, then $\mathrm{parallel}\ S$ terminates. If $a \in \mathrm{parallel}\ S$, then $a \in c$ for some $c$ in $S$.

*Proof.* The state of the parallel run is a finite list $L$ of running computations and the rest $S'$ of the weak sequence. At each tick, the run destructs each computation in $L$. If one of them gives a value, the run stops with it. Otherwise it replaces each one by its tail, reads one entry of $S'$, and adds the computation of that entry to $L$ when the entry is an element. Each computation in $L$ is a tail of a computation in $S$, and a tail has the same results as the computation.

First claim. Let $c$ be the element of $S$ at index $i$, with $\mathrm{Results}\ c\ a\ N$. After $i + 1$ ticks, a tail of $c$ is in $L$ or the run has stopped. After each further tick, the tail in $L$ advances by one step. So after at most $i + 1 + N$ ticks, the tail of $c$ gives $a$ or the run has stopped earlier. In both cases, the run stops.

Second claim. The run stops only when some computation in $L$ gives a value $a$. That computation is a tail of some $c$ in $S$, so $a \in c$. $\square$

The result of a parallel run depends on the timing. If two computations in $S$ have different results, the faster one wins. Replacing one of them by an equivalent but slower computation can change the result. So parallel does not respect equivalence; the module documentation says this explicitly.

**Proposition (The weak sequence monad is not lawful).** There are $a$ and $f$ with $\mathrm{bind}(\mathrm{ret}\ a)\ f \neq f(a)$, but $\mathrm{bind}(\mathrm{ret}\ a)\ f \sim^w f(a)$ for all $a$ and $f$.

*Proof.* By definition, $\mathrm{ret}\ a = \mathrm{cons}\ a\ \mathrm{nil}$ and $\mathrm{bind}\ s\ f = \mathrm{join}(\mathrm{map}\ f\ s)$. Mathlib defines join so that each piece costs one tick: $\mathrm{join}(\mathrm{cons}\ s\ S) = \mathrm{think}(\mathrm{append}\ s\ (\mathrm{join}\ S))$. So $\mathrm{bind}(\mathrm{ret}\ a)\ f = \mathrm{join}(\mathrm{cons}(f\ a)\ \mathrm{nil}) = \mathrm{think}(\mathrm{append}(f\ a)\ \mathrm{nil}) = \mathrm{think}(f\ a)$. Take $f(a) = \mathrm{nil}$. Then the left side has the entry $\mathrm{some}\ \mathrm{none}$ at $0$, and the right side has the entry $\mathrm{none}$ at $0$. So they differ. For the equivalence, $\mathrm{think}\ s \sim^w s$: the destruct of $\mathrm{think}\ s$ is the think of the destruct of $s$, and the two destructs are equivalent computations by the previous proposition. The relation $C\ s'\ t' :\iff s' = t'$ then closes the definition of $\mathrm{LiftRel}$. $\square$

**Proposition (Bind and purity of semiquotients).** For a semiquotient $q$ and $f : \alpha \to \mathrm{Semiquot}\ \beta$, $b \in \mathrm{bind}\ q\ f$ if and only if $b \in f(a)$ for some $a \in q$. For an inhabited $\alpha$, the semiquotient with the set $\alpha$ is pure if and only if $\alpha$ has at most one element.

*Proof.* The set of $\mathrm{bind}\ q\ f$ is the union of the sets of $f(a)$ over $a$ in the set of $q$, so the first claim is the definition of a union. For the second claim, the semiquotient $\mathrm{univ}$ is pure when $a = b$ for all $a, b \in \alpha$, which is the definition of a subsingleton. $\square$

### Examples

**Example (A computation that terminates after three steps).** Let $c = \mathrm{thinkN}(\mathrm{pure}\ 5)\ 3$. The entries are $c(0) = c(1) = c(2) = \mathrm{none}$ and $c(n) = \mathrm{some}\ 5$ for $n \geq 3$. So $5 \in c$, the length is $3$ and $\mathrm{get}\ c = 5$. The computation is equivalent to $\mathrm{pure}\ 5$, but it is not equal to it, because the entries at $0$ differ.

**Example (A bind).** Let $c = \mathrm{think}(\mathrm{pure}\ 2)$ and $f(n) = \mathrm{thinkN}(\mathrm{pure}(n + 1))\ 2$. Then $\mathrm{Results}\ c\ 2\ 1$ and $\mathrm{Results}(f\ 2)\ 3\ 2$. The theorem on bind gives $\mathrm{Results}(\mathrm{bind}\ c\ f)\ 3\ 3$, and in fact $\mathrm{bind}\ c\ f = \mathrm{thinkN}(\mathrm{pure}\ 3)\ 3$.

**Counterexample (A computation that never terminates).** The computation $\mathrm{empty}$ has no result, so it does not terminate. Each bind with it fails too: $\mathrm{bind}\ \mathrm{empty}\ f = \mathrm{empty}$, because $\mathrm{empty} = \mathrm{think}\ \mathrm{empty}$ and bind commutes with think. The choice operator $\mathrm{orElse}$ runs two computations in parallel and returns the first result, so $\mathrm{orElse}\ \mathrm{empty}\ c = c$.

**Example (A parallel run).** Let $S = \mathrm{ofList}[\mathrm{empty}, \mathrm{thinkN}(\mathrm{pure}\ 7)\ 2]$. Tick 1 starts $\mathrm{empty}$. Tick 2 advances it and starts the second computation $d$. Tick 3 advances both, so $d$ becomes $\mathrm{think}(\mathrm{pure}\ 7)$. Tick 4 advances $d$ to $\mathrm{pure}\ 7$. At tick 5 the run sees the value $7$ and stops. So $\mathrm{parallel}\ S = \mathrm{thinkN}(\mathrm{pure}\ 7)\ 4$. A sequential search on $S$ never leaves $\mathrm{empty}$.

**Example (A semiquotient).** The semiquotient $\mathrm{pure}\ 3$ over $\mathbb{N}$ has the set $\{3\}$ and is pure. The semiquotient $\mathrm{blur}\{1, 2\}(\mathrm{pure}\ 3)$ has the set $\{1, 2, 3\}$. Two semiquotients with the same set are equal, so this semiquotient equals $\mathrm{blur}\{2, 3\}(\mathrm{pure}\ 1)$. The witness $3$ is forgotten, and the semiquotient models a choice among three values.

### The library around it

::: mathlib
`Computation` · `Mathlib.Data.Seq.Computation`

`Computation α` is the subtype of `Stream' (Option α)` of the text. The constructors are `Computation.pure`, `Computation.think`, `Computation.thinkN` and `Computation.empty`, with `Computation.think_empty`. `Computation.destruct`, `Computation.corec` and `Computation.corec_eq` give the coinductive interface, and `Computation.runFor` reads the state after `n` ticks. Membership `Computation.Mem` comes with `Computation.mem_unique`.

<?decl Computation?>
:::

::: mathlib
`Computation.Results` · `Mathlib.Data.Seq.Computation`

`Computation.Terminates` is a class, so `Computation.get` and `Computation.length` find the proof by instance search; `Computation.get_mem` states that the value is a result. `Computation.Results` packs a result with its time, and `Computation.Results.len_unique`, `Computation.results_thinkN`, `Computation.results_thinkN_pure` and `Computation.length_thinkN` are the lemmas of the text. `Computation.not_terminates_empty` records the failure of `empty`.

<?decl Computation.Results?>
:::

::: mathlib
`Computation.results_bind` · `Mathlib.Data.Seq.Computation`

`Computation.bind` and `Computation.monad` give the monad, with the laws `Computation.ret_bind`, `Computation.bind_pure` and `Computation.bind_assoc`, and the step `Computation.think_bind`. `Computation.mem_bind`, `Computation.results_bind` and `Computation.length_bind` track results and times. `Computation.orElse` is the parallel choice, with `Computation.ret_orElse`, `Computation.orElse_pure`, `Computation.orElse_think`, `Computation.empty_orElse` and `Computation.orElse_empty`.

<?decl Computation.results_bind?>
:::

::: mathlib
`Computation.Equiv` · `Mathlib.Data.Seq.Computation`

`Computation.Equiv` is written `~`, with `Computation.think_equiv`, `Computation.thinkN_equiv`, `Computation.bind_congr` and `Computation.equiv_pure_of_mem`. `Computation.LiftRel` lifts a relation, and `Computation.lift_eq_iff_equiv` identifies the lift of equality with equivalence. `Computation.Promises` is written `~>`.

<?decl Computation.Equiv?>
:::

::: mathlib
`Computation.parallel` · `Mathlib.Data.Seq.Parallel`

`Computation.parallel` takes a weak sequence of computations. `Computation.terminates_parallel` and `Computation.exists_of_mem_parallel` are the two claims of the theorem, and `Computation.mem_parallel` and `Computation.parallel_promises` handle the case in which all computations promise the same value. `Computation.map_parallel` and `Computation.parallel_congr_left` give compatibility with map and with a pointwise equivalence that keeps the promise.

<?decl Computation.parallel?>
:::

::: mathlib
`Stream'.WSeq` · `Mathlib.Data.WSeq.Basic`

`Stream'.WSeq α` is `Seq (Option α)`, with `Stream'.WSeq.nil`, `Stream'.WSeq.cons`, `Stream'.WSeq.think` and `Stream'.WSeq.destruct`. The observations `Stream'.WSeq.head`, `Stream'.WSeq.tail`, `Stream'.WSeq.get?` and `Stream'.WSeq.toList` return computations. `Stream'.WSeq.ofSeq` and `Stream'.WSeq.ofList` embed sequences and lists. The operations `Stream'.WSeq.append`, `Stream'.WSeq.map`, `Stream'.WSeq.join`, `Stream'.WSeq.ret` and `Stream'.WSeq.bind` give the instance `Stream'.WSeq.monad`, which is not lawful. `Stream'.WSeq.join_cons` and `Stream'.WSeq.join_think` show the extra tick. `Mathlib.Data.WSeq.Defs` adds `Stream'.WSeq.length` and `Stream'.WSeq.IsFinite`.

<?decl Stream'.WSeq.join_cons?>
:::

::: mathlib
`Stream'.WSeq.Equiv` · `Mathlib.Data.WSeq.Relation`

`Stream'.WSeq.LiftRelO` is the case condition, `Stream'.WSeq.LiftRel` is the coinductive lift, and `Stream'.WSeq.Equiv` is written `~ʷ`. The monad laws hold up to `~ʷ`: `Stream'.WSeq.ret_bind`, `Stream'.WSeq.bind_ret`, `Stream'.WSeq.bind_assoc` and `Stream'.WSeq.join_ret`, with `Stream'.WSeq.think_equiv` as the basic step.

<?decl Stream'.WSeq.think_equiv?>
:::

::: mathlib
`Stream'.WSeq.Productive` · `Mathlib.Data.WSeq.Productive`

`Stream'.WSeq.Productive` is a class with `Stream'.WSeq.productive_iff`. A productive weak sequence becomes a sequence by `Stream'.WSeq.toSeq`, and `Stream'.WSeq.productive_ofSeq` gives the instance for sequences without ticks.

<?decl Stream'.WSeq.Productive?>
:::

::: mathlib
`Semiquot` · `Mathlib.Data.Semiquot`

`Semiquot α` has the fields `s` and `val`. `Semiquot.pure`, `Semiquot.map`, `Semiquot.bind` and `Semiquot.blur` are the operations of the text, with `Semiquot.mem_bind` and the instance `Semiquot.instLawfulMonad`. `Semiquot.IsPure`, `Semiquot.get`, `Semiquot.univ` and `Semiquot.isPure_univ` handle purity.

<?decl Semiquot.mem_bind?>
:::

Common errors of a learner: The first error is to prove that two computations are equal when they are only equivalent; `think c = c` is false, and `think c ~ c` is the true statement. The second error is to expect `Computation.get` to need no hypothesis; it needs a `Terminates` instance. The third error is to use the `Stream'.WSeq.monad` laws as rewriting rules; the laws hold only up to `~ʷ`. The fourth error is to transport a result of `Computation.parallel` along an equivalence of the input computations; the result can change. The fifth error is to read a semiquotient as a quotient; the set can grow under `blur`, and only pure semiquotients give a value.

### Exercises

1. (A) Write the first five entries of $\mathrm{thinkN}(\mathrm{pure}\ 4)\ 2$ and of $\mathrm{think}(\mathrm{thinkN}(\mathrm{pure}\ 4)\ 2)$. Give the length and the result of each. Hint: think adds one $\mathrm{none}$ in front.
2. (A) Compute $\mathrm{bind}(\mathrm{thinkN}(\mathrm{pure}\ 1)\ 2)(\lambda n.\ \mathrm{thinkN}(\mathrm{pure}(2n))\ 3)$. Hint: use the theorem on bind.
3. (A) Show that $\mathrm{orElse}(\mathrm{thinkN}(\mathrm{pure}\ 1)\ 3)(\mathrm{thinkN}(\mathrm{pure}\ 2)\ 1) = \mathrm{think}(\mathrm{pure}\ 2)$. Hint: apply the lemma for two thinks once, and then the lemma for a think and a pure.
4. (B) Prove that $c \sim \mathrm{pure}\ a$ whenever $a \in c$. Hint: use uniqueness of results in both directions.
5. (B) Prove that $c_1 \sim c_2$ and $f_1(a) \sim f_2(a)$ for all $a$ imply $\mathrm{bind}\ c_1\ f_1 \sim \mathrm{bind}\ c_2\ f_2$. Hint: write a result of a bind as a result $a$ of the first computation followed by a result of $f(a)$.
6. (B) Find two weak sequences $S, S'$ of computations of the same length with equivalent entries at each index, such that $\mathrm{parallel}\ S$ and $\mathrm{parallel}\ S'$ have different results. Hint: take $S' = \mathrm{ofList}[\mathrm{pure}\ 0, \mathrm{pure}\ 1]$, and replace $\mathrm{pure}\ 0$ by $\mathrm{thinkN}(\mathrm{pure}\ 0)\ 5$ in $S$.
7. (C) Show that a weak sequence with infinitely many consecutive ticks after its first element is not productive, and that each sequence of the previous section gives a productive weak sequence. Hint: the computation $\mathrm{get?}\ s\ 1$ waits for the second element.

### Notes and history

Moggi proposed monads as a structure for computational effects in 1989 and 1991, and partiality is one of his examples. The computation type of Mathlib is the delay monad in this tradition. Its equality distinguishes the time of a result, and its equivalence forgets that time. Weak sequences add time between elements; they serve as the target of operations such as filter, and as the input of parallel search.

The Mathlib files are by these authors, read from their headers: `Mathlib.Data.Seq.Computation`, `Mathlib.Data.Seq.Parallel`, `Mathlib.Data.WSeq.Defs`, `Mathlib.Data.WSeq.Basic`, `Mathlib.Data.WSeq.Productive`, `Mathlib.Data.WSeq.Relation` and `Mathlib.Data.Semiquot` by Mario Carneiro.

### Reference

<?reference?>
