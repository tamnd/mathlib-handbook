---
title: Possibly finite sequences
kind: theory
modules:
  - Mathlib.Data.Seq.Defs
  - Mathlib.Data.Seq.Basic
explains:
  E3: [Stream'.Seq, Stream'.IsSeq, Stream'.Seq.destruct, Stream'.Seq.corec, Stream'.Seq.corec_eq, Stream'.Seq.IsBisimulation, Stream'.Seq.coinduction, Stream'.Seq.Terminates, Stream'.Seq.append, Stream'.Seq.join, Stream'.Seq.append_assoc, Stream'.Seq.join_cons, Stream'.Seq.take, Stream'.Seq.ofList]
  E2: [Stream'.Seq.nil, Stream'.Seq.cons, "Stream'.Seq.get?", Stream'.Seq.head, Stream'.Seq.tail, Stream'.Seq.BisimO, Stream'.Seq.coinduction2, Stream'.Seq.TerminatedAt, Stream'.Seq.length, Stream'.Seq.length', Stream'.Seq.ofStream, Stream'.Seq.toList, Stream'.Seq.toStream, Stream'.Seq.map, Stream'.Seq.cons_append, Stream'.Seq.nil_append, Stream'.Seq.append_nil, Stream'.Seq.map_append, Stream'.Seq.join_nil, Stream'.Seq.join_append, Stream'.Seq.ofList_append, Stream'.Seq.terminates_ofList, Stream'.Seq.terminatedAt_ofList, Stream'.Seq.toList_ofList, "Stream'.Seq.ofList_get?", Stream'.Seq.map_comp, Stream'.Seq.map_id, Stream'.Seq.destruct_nil, Stream'.Seq.destruct_cons, Stream'.Seq.destruct_eq_none, Stream'.Seq.destruct_eq_cons, Stream'.Seq.corec_nil, Stream'.Seq.corec_cons, Stream'.Seq.not_terminates_iff, Stream'.Seq.ge_stable, Stream'.Seq.terminates_cons_iff, Stream'.Seq.length_cons, Stream'.Seq.take_zero, Stream'.Seq.take_succ_cons, Stream'.Seq1, Stream'.Seq1.ret, Stream'.Seq1.bind, Stream'.Seq1.lawfulMonad]
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

## Possibly finite sequences

### Overview

A list is finite, and a stream is infinite. Many programs produce a sequence that can stop or can continue for ever, such as the terms of a continued fraction. The type `Stream'.Seq α` of Mathlib holds such sequences. An element of this type is a stream of options in which `none` marks the end. After the first `none`, all entries are `none`.

The type has two faces. Inside, it is a subtype of `Stream' (Option α)`. Outside, it is a coinductive type: each sequence is empty or a head followed by a tail, and the function `destruct` makes this case split. A definition by corecursion gives a sequence from a seed and a step function. A proof by bisimulation shows that two sequences are equal when their heads agree and their tails stay related.

This section defines the type and proves the coinduction principle. It then proves that append is associative, and treats termination, lists, `map` and `join`. Section 2 builds computations and weak sequences on top of this type.

### Definitions

**Definition (Sequence condition).** A stream $f : \mathbb{N} \to \mathrm{Option}\ \alpha$ satisfies the sequence condition when $f(n) = \mathrm{none}$ implies $f(n+1) = \mathrm{none}$ for each $n$. By induction, $f(n) = \mathrm{none}$ then implies $f(m) = \mathrm{none}$ for all $m \geq n$.

**Definition (Sequence).** The type $\mathrm{Seq}\ \alpha$ is the subtype of streams $f : \mathbb{N} \to \mathrm{Option}\ \alpha$ that satisfy the sequence condition. For $s : \mathrm{Seq}\ \alpha$, the value $\mathrm{get?}\ s\ n$ is the entry $s(n)$. The head of $s$ is $\mathrm{get?}\ s\ 0$, and the tail of $s$ is the shifted stream $n \mapsto s(n+1)$.

**Definition (Empty sequence and cons).** The empty sequence $\mathrm{nil}$ is the constant stream $\mathrm{none}$. For $a : \alpha$ and $s : \mathrm{Seq}\ \alpha$, the sequence $\mathrm{cons}\ a\ s$ is the stream with entry $\mathrm{some}\ a$ at $0$ and entry $s(n)$ at $n + 1$.

Both streams satisfy the sequence condition; for $\mathrm{cons}\ a\ s$, the condition at $n + 1$ is the condition of $s$ at $n$. The tail of $\mathrm{nil}$ is $\mathrm{nil}$, and the tail of $\mathrm{cons}\ a\ s$ is $s$.

**Definition (Destruct).** The function $\mathrm{destruct} : \mathrm{Seq}\ \alpha \to \mathrm{Option}(\alpha \times \mathrm{Seq}\ \alpha)$ sends $s$ to $\mathrm{none}$ when the head of $s$ is $\mathrm{none}$, and to $\mathrm{some}(a, \mathrm{tail}\ s)$ when the head of $s$ is $\mathrm{some}\ a$.

So $\mathrm{destruct}\ \mathrm{nil} = \mathrm{none}$ and $\mathrm{destruct}(\mathrm{cons}\ a\ s) = \mathrm{some}(a, s)$. Each sequence is $\mathrm{nil}$ or a cons: if $\mathrm{destruct}\ s = \mathrm{none}$, then the head is $\mathrm{none}$, so all entries are $\mathrm{none}$ and $s = \mathrm{nil}$. If $\mathrm{destruct}\ s = \mathrm{some}(a, t)$, then $s = \mathrm{cons}\ a\ t$ by comparison of entries.

**Definition (Corecursion).** Let $\beta$ be a type of seeds and $f : \beta \to \mathrm{Option}(\alpha \times \beta)$ a step function. The sequence $\mathrm{corec}\ f\ b$ is the sequence that the step function produces from the seed $b$: if $f(b) = \mathrm{none}$, it is empty; if $f(b) = \mathrm{some}(a, b')$, it has head $a$ and continues as $\mathrm{corec}\ f\ b'$.

**Definition (Bisimulation).** A relation $R$ on $\mathrm{Seq}\ \alpha$ is a bisimulation when, for all $s_1, s_2$ with $R\ s_1\ s_2$, one of two cases holds. Either $\mathrm{destruct}\ s_1 = \mathrm{destruct}\ s_2 = \mathrm{none}$, or $\mathrm{destruct}\ s_1 = \mathrm{some}(a, t_1)$ and $\mathrm{destruct}\ s_2 = \mathrm{some}(a, t_2)$ with the same $a$ and with $R\ t_1\ t_2$. Mathlib calls the case condition $\mathrm{BisimO}\ R$.

**Definition (Termination and length).** A sequence $s$ is terminated at $n$ when $\mathrm{get?}\ s\ n = \mathrm{none}$. It terminates when it is terminated at some $n$. For a terminating $s$, the length of $s$ is the least $n$ at which $s$ is terminated.

The predicate "terminated at $n$" is decidable. The predicate "terminates" is not decidable in general.

**Definition (Lists, streams and take).** For a list $l$, the sequence $\mathrm{ofList}\ l$ has the entry $l[n]?$ at $n$. For a stream $x$, the sequence $\mathrm{ofStream}\ x$ has the entry $\mathrm{some}(x\ n)$ at $n$. The function $\mathrm{take}\ n\ s$ gives the list of the first entries of $s$, at most $n$ of them: $\mathrm{take}\ 0\ s = []$, and $\mathrm{take}(n+1)\ s$ is $[]$ when $\mathrm{destruct}\ s = \mathrm{none}$ and $a :: \mathrm{take}\ n\ t$ when $\mathrm{destruct}\ s = \mathrm{some}(a, t)$. For a terminating $s$, $\mathrm{toList}\ s = \mathrm{take}(\mathrm{length}\ s)\ s$.

**Definition (Append, map and join).** The sequence $\mathrm{append}\ s_1\ s_2$ is the corecursion on pairs with the step: if $\mathrm{destruct}\ s_1 = \mathrm{some}(a, s_1')$, emit $a$ and continue with $(s_1', s_2)$; if $s_1$ is empty and $\mathrm{destruct}\ s_2 = \mathrm{some}(b, s_2')$, emit $b$ and continue with $(\mathrm{nil}, s_2')$; if both are empty, stop. The sequence $\mathrm{map}\ g\ s$ applies $\mathrm{Option.map}\ g$ at each entry. A nonempty sequence is a pair $(a, s)$ of a head and a sequence; Mathlib calls this type $\mathrm{Seq1}\ \alpha$. The function $\mathrm{join} : \mathrm{Seq}(\mathrm{Seq1}\ \alpha) \to \mathrm{Seq}\ \alpha$ concatenates a sequence of nonempty sequences.

The pieces of a join are nonempty for a reason. A join of pieces that can be empty can meet infinitely many empty pieces and never decide its next entry. With nonempty pieces, each step of the corecursion emits one entry.

### Theorems and proofs

**Lemma (Equations of corecursion).** For each step function $f$ and seed $b$, $\mathrm{destruct}(\mathrm{corec}\ f\ b) = \mathrm{Option.map}(\mathrm{id} \times \mathrm{corec}\ f)(f\ b)$. In particular, $f(b) = \mathrm{none}$ gives $\mathrm{corec}\ f\ b = \mathrm{nil}$, and $f(b) = \mathrm{some}(a, b')$ gives $\mathrm{corec}\ f\ b = \mathrm{cons}\ a\ (\mathrm{corec}\ f\ b')$.

*Proof.* Mathlib runs the step on the states $\mathrm{Option}\ \beta$: the state $\mathrm{none}$ stays $\mathrm{none}$ and gives the entry $\mathrm{none}$, and the state $\mathrm{some}\ b$ gives the first component of $f(b)$ as entry and the second component as the next state. The sequence $\mathrm{corec}\ f\ b$ is the stream of entries from the state $\mathrm{some}\ b$. Case 1: $f(b) = \mathrm{none}$. The entry at $0$ is $\mathrm{none}$, so the head is $\mathrm{none}$ and $\mathrm{destruct}$ gives $\mathrm{none}$, which is the right side. Case 2: $f(b) = \mathrm{some}(a, b')$. The entry at $0$ is $\mathrm{some}\ a$, and the next state is $\mathrm{some}\ b'$. The tail of the stream is the stream of the state machine that starts at $\mathrm{some}\ b'$, which is $\mathrm{corec}\ f\ b'$. So $\mathrm{destruct}$ gives $\mathrm{some}(a, \mathrm{corec}\ f\ b')$, which is the right side. The two special cases follow from the characterization of $\mathrm{nil}$ and $\mathrm{cons}$ by $\mathrm{destruct}$. $\square$

**Theorem (Coinduction).** Let $R$ be a bisimulation on $\mathrm{Seq}\ \alpha$. If $R\ s_1\ s_2$, then $s_1 = s_2$.

*Proof.* It suffices to show that $\mathrm{get?}\ s_1\ n = \mathrm{get?}\ s_2\ n$ for each $n$, because two elements of a subtype of a function type are equal when the functions agree at each point. The proof is by induction on $n$, for all pairs related by $R$ at once.

Step 1, $n = 0$. Take $s_1, s_2$ with $R\ s_1\ s_2$. If both destructs are $\mathrm{none}$, both heads are $\mathrm{none}$. If $\mathrm{destruct}\ s_1 = \mathrm{some}(a, t_1)$ and $\mathrm{destruct}\ s_2 = \mathrm{some}(a, t_2)$, both heads are $\mathrm{some}\ a$. The bisimulation condition excludes the mixed cases.

Step 2, from $n$ to $n + 1$. The entry $\mathrm{get?}\ s\ (n+1)$ is $\mathrm{get?}(\mathrm{tail}\ s)\ n$. Take $s_1, s_2$ with $R\ s_1\ s_2$. If both destructs are $\mathrm{none}$, then $s_1 = s_2 = \mathrm{nil}$ and the entries agree. In the other case, $s_1 = \mathrm{cons}\ a\ t_1$ and $s_2 = \mathrm{cons}\ a\ t_2$ with $R\ t_1\ t_2$. The tails are $t_1$ and $t_2$, and the induction hypothesis for the pair $(t_1, t_2)$ gives $\mathrm{get?}\ t_1\ n = \mathrm{get?}\ t_2\ n$. $\square$

**Theorem (Append is associative).** For all $s, t, u : \mathrm{Seq}\ \alpha$, $\mathrm{append}(\mathrm{append}\ s\ t)\ u = \mathrm{append}\ s\ (\mathrm{append}\ t\ u)$.

*Proof.* First record four equations that follow from the lemma on corecursion and the definition of append: $\mathrm{append}\ \mathrm{nil}\ \mathrm{nil} = \mathrm{nil}$, $\mathrm{append}\ \mathrm{nil}\ (\mathrm{cons}\ b\ v) = \mathrm{cons}\ b\ (\mathrm{append}\ \mathrm{nil}\ v)$, $\mathrm{append}(\mathrm{cons}\ a\ v)\ w = \mathrm{cons}\ a\ (\mathrm{append}\ v\ w)$, and $\mathrm{append}\ \mathrm{nil}\ v = v$. The last equation needs its own bisimulation, with the relation $s_1 = \mathrm{append}\ \mathrm{nil}\ v$ and $s_2 = v$, and a case split on $v$.

Let $R\ s_1\ s_2$ hold when there are $s, t, u$ with $s_1 = \mathrm{append}(\mathrm{append}\ s\ t)\ u$ and $s_2 = \mathrm{append}\ s\ (\mathrm{append}\ t\ u)$. The pair of the goal is in $R$. It remains to show that $R$ is a bisimulation. Take a pair given by $s, t, u$, and split on $s$.

Case 1: $s = \mathrm{cons}\ a\ s'$. Then $s_1 = \mathrm{cons}\ a\ (\mathrm{append}(\mathrm{append}\ s'\ t)\ u)$ and $s_2 = \mathrm{cons}\ a\ (\mathrm{append}\ s'\ (\mathrm{append}\ t\ u))$. The heads agree, and the tails are in $R$ with the witnesses $s', t, u$.

Case 2: $s = \mathrm{nil}$. Then $s_1 = \mathrm{append}\ t\ u$ and $s_2 = \mathrm{append}\ t\ u$ by the fourth equation. Split on $t$. If $t = \mathrm{cons}\ b\ t'$, both sides are $\mathrm{cons}\ b\ (\mathrm{append}\ t'\ u)$, and the tails are in $R$ with the witnesses $\mathrm{nil}, t', u$. If $t = \mathrm{nil}$, both sides are $u$. Split on $u$. If $u = \mathrm{nil}$, both destructs are $\mathrm{none}$. If $u = \mathrm{cons}\ c\ u'$, both sides have head $c$ and tail $u'$, and the pair $(u', u')$ is in $R$ with the witnesses $\mathrm{nil}, \mathrm{nil}, u'$.

So $R$ is a bisimulation, and the theorem on coinduction gives the equation. $\square$

**Proposition (An infinite sequence absorbs append).** If $s$ does not terminate, then $\mathrm{append}\ s\ t = s$ for each $t$.

*Proof.* Let $R\ s_1\ s_2$ hold when there is a sequence $v$ that does not terminate with $s_1 = \mathrm{append}\ v\ t$ and $s_2 = v$. The pair of the goal is in $R$. Take a pair given by $v$. The sequence $v$ is not $\mathrm{nil}$, because $\mathrm{nil}$ is terminated at $0$. So $v = \mathrm{cons}\ a\ v'$. Then $s_1 = \mathrm{cons}\ a\ (\mathrm{append}\ v'\ t)$ and $s_2 = \mathrm{cons}\ a\ v'$. The heads agree. The sequence $v'$ does not terminate: if $v'$ were terminated at $n$, then $v$ would be terminated at $n + 1$. So the tails are in $R$ with the witness $v'$, and coinduction gives the result. $\square$

**Proposition (Lists round trip).** For each list $l$, the sequence $\mathrm{ofList}\ l$ terminates, its length is the length of $l$, and $\mathrm{toList}(\mathrm{ofList}\ l) = l$.

*Proof.* The entry of $\mathrm{ofList}\ l$ at $n$ is $l[n]?$, which is $\mathrm{none}$ exactly when $n \geq |l|$. So the sequence is terminated at $|l|$, and the least such index is $|l|$, because the entries at $n < |l|$ are $\mathrm{some}$. For the round trip, show $\mathrm{take}\ n\ (\mathrm{ofList}\ l) = l.\mathrm{take}\ n$ by induction on $n$ with $l$ general. For $n = 0$, both sides are $[]$. For $n + 1$: if $l = []$, then $\mathrm{ofList}\ l = \mathrm{nil}$, and both sides are $[]$. If $l = x :: l'$, then $\mathrm{ofList}\ l = \mathrm{cons}\ x\ (\mathrm{ofList}\ l')$, and $\mathrm{take}(n+1)$ gives $x :: \mathrm{take}\ n\ (\mathrm{ofList}\ l')$, which is $x :: l'.\mathrm{take}\ n$ by the hypothesis. At $n = |l|$, the right side is $l$. $\square$

**Proposition (Join of a cons).** For $a : \alpha$, $s : \mathrm{Seq}\ \alpha$ and $S : \mathrm{Seq}(\mathrm{Seq1}\ \alpha)$, $\mathrm{join}(\mathrm{cons}(a, s)\ S) = \mathrm{cons}\ a\ (\mathrm{append}\ s\ (\mathrm{join}\ S))$.

*Proof.* Let $R\ s_1\ s_2$ hold when $s_1 = s_2$ or there are $a, s, S$ with $s_1 = \mathrm{join}(\mathrm{cons}(a, s)\ S)$ and $s_2 = \mathrm{cons}\ a\ (\mathrm{append}\ s\ (\mathrm{join}\ S))$. Equal sequences have equal destructs and equal tails. Take a pair of the second kind. By the definition of join, $s_1$ has head $a$, and its tail is $\mathrm{join}\ S$ when $s = \mathrm{nil}$, and $\mathrm{join}(\mathrm{cons}(b, s')\ S)$ when $s = \mathrm{cons}\ b\ s'$. The sequence $s_2$ has head $a$ and tail $\mathrm{append}\ s\ (\mathrm{join}\ S)$. If $s = \mathrm{nil}$, the tail of $s_2$ is $\mathrm{join}\ S$, so the tails are equal. If $s = \mathrm{cons}\ b\ s'$, the tail of $s_2$ is $\mathrm{cons}\ b\ (\mathrm{append}\ s'\ (\mathrm{join}\ S))$, and the tails form a pair of the second kind with the witnesses $b, s', S$. Coinduction gives the equation. $\square$

### Examples

**Example (A finite sequence).** Let $s = \mathrm{ofList}[1, 2, 3]$. The entries are $\mathrm{get?}\ s\ 0 = \mathrm{some}\ 1$, $\mathrm{get?}\ s\ 1 = \mathrm{some}\ 2$, $\mathrm{get?}\ s\ 2 = \mathrm{some}\ 3$, and $\mathrm{none}$ at each $n \geq 3$. So $s$ terminates with length $3$. The definition of take gives $\mathrm{take}\ 2\ s = [1, 2]$ and $\mathrm{take}\ 5\ s = [1, 2, 3]$, because the third step meets $\mathrm{destruct} = \mathrm{none}$ and stops.

**Example (A sequence from corecursion).** Let $f(n) = \mathrm{some}(n, n + 1)$ when $n < 3$ and $f(n) = \mathrm{none}$ when $n \geq 3$. The lemma on corecursion gives $\mathrm{corec}\ f\ 0 = \mathrm{cons}\ 0\ (\mathrm{corec}\ f\ 1) = \mathrm{cons}\ 0\ (\mathrm{cons}\ 1\ (\mathrm{cons}\ 2\ (\mathrm{corec}\ f\ 3)))$, and $\mathrm{corec}\ f\ 3 = \mathrm{nil}$. So $\mathrm{corec}\ f\ 0 = \mathrm{ofList}[0, 1, 2]$. With the step $g(n) = \mathrm{some}(n, n + 1)$ for all $n$, the sequence $\mathrm{corec}\ g\ 0$ has entry $\mathrm{some}\ n$ at $n$. This is the sequence $\mathrm{nats}$, which does not terminate.

**Example (Join).** Let $S = \mathrm{ofList}[(1, \mathrm{ofList}[2]), (3, \mathrm{nil})]$. The proposition on join gives $\mathrm{join}\ S = \mathrm{cons}\ 1\ (\mathrm{append}(\mathrm{ofList}[2])(\mathrm{join}(\mathrm{ofList}[(3, \mathrm{nil})])))$. The inner join is $\mathrm{cons}\ 3\ (\mathrm{append}\ \mathrm{nil}\ \mathrm{nil}) = \mathrm{ofList}[3]$. So $\mathrm{join}\ S = \mathrm{cons}\ 1\ (\mathrm{ofList}[2, 3]) = \mathrm{ofList}[1, 2, 3]$.

**Counterexample (Append does not reach the second part).** Let $t = \mathrm{ofList}[7]$. By the proposition on infinite sequences, $\mathrm{append}\ \mathrm{nats}\ t = \mathrm{nats}$. The entry $7$ of $t$ never appears at any index. The length formula of lists holds only when the first part terminates.

### The library around it

::: mathlib
`Stream'.Seq` · `Mathlib.Data.Seq.Defs`

`Stream'.IsSeq` is the sequence condition, and `Stream'.Seq α` is the subtype of `Stream' (Option α)` that satisfies it. The constructors are `Stream'.Seq.nil` and `Stream'.Seq.cons`, and the observations are `Stream'.Seq.get?`, `Stream'.Seq.head`, `Stream'.Seq.tail` and `Stream'.Seq.destruct`. `Stream'.Seq.destruct_nil`, `Stream'.Seq.destruct_cons`, `Stream'.Seq.destruct_eq_none` and `Stream'.Seq.destruct_eq_cons` give the case analysis. The type `Stream'.Seq1 α` is `α × Seq α`.

<?decl Stream'.Seq?>
:::

::: mathlib
`Stream'.Seq.corec` · `Mathlib.Data.Seq.Defs`

`Stream'.Seq.corec f b` builds a sequence from the step `f : β → Option (α × β)`. The equation `Stream'.Seq.corec_eq` states `destruct (corec f b) = omap (corec f) (f b)`, and `Stream'.Seq.corec_nil` and `Stream'.Seq.corec_cons` give the two cases.

<?decl Stream'.Seq.corec_eq?>
:::

::: mathlib
`Stream'.Seq.coinduction` · `Mathlib.Data.Seq.Defs`

`Stream'.Seq.BisimO` is the case condition, and `Stream'.Seq.IsBisimulation R` asks it for each related pair. The theorem of coinduction in the text is the lemma eq_of_bisim of this module; the index of this edition has no declaration for that name, so this box cites its neighbours. `Stream'.Seq.coinduction` proves equality from equal heads and from a closure property of tails, and `Stream'.Seq.coinduction2` is the form for two functions of a sequence.

<?decl Stream'.Seq.coinduction?>
:::

::: mathlib
`Stream'.Seq.Terminates` · `Mathlib.Data.Seq.Defs`

`Stream'.Seq.TerminatedAt s n` is `s.get? n = none`, and it is decidable. `Stream'.Seq.Terminates` is the existential statement, with `Stream'.Seq.not_terminates_iff`, `Stream'.Seq.ge_stable` and `Stream'.Seq.terminates_cons_iff`. `Stream'.Seq.length` takes a proof of termination and returns the least index, and `Stream'.Seq.length'` returns a value in `ℕ∞` with no proof. `Stream'.Seq.length_cons` adds one for a cons.

<?decl Stream'.Seq.Terminates?>
:::

::: mathlib
`Stream'.Seq.ofList` · `Mathlib.Data.Seq.Defs`

`Stream'.Seq.ofList` and `Stream'.Seq.ofStream` embed lists and streams, and `Stream'.Seq.ofList_get?` gives the entries. `Stream'.Seq.take` takes a prefix, with `Stream'.Seq.take_zero` and `Stream'.Seq.take_succ_cons`. `Stream'.Seq.toList` needs a proof of termination, and `Stream'.Seq.toStream` needs a proof of non-termination. In `Mathlib.Data.Seq.Basic`, the lemmas `Stream'.Seq.terminatedAt_ofList`, `Stream'.Seq.terminates_ofList` and `Stream'.Seq.toList_ofList` give the round trip of the text.

<?decl Stream'.Seq.ofList?>
:::

::: mathlib
`Stream'.Seq.append_assoc` · `Mathlib.Data.Seq.Basic`

`Stream'.Seq.append` is defined by corecursion on pairs. The lemmas `Stream'.Seq.cons_append`, `Stream'.Seq.nil_append`, `Stream'.Seq.append_nil` and `Stream'.Seq.append_assoc` follow the proofs of the text. `Stream'.Seq.map` acts entry by entry, with `Stream'.Seq.map_id`, `Stream'.Seq.map_comp` and `Stream'.Seq.map_append`, and `Stream'.Seq.ofList_append` compares append with list append.

<?decl Stream'.Seq.append_assoc?>
:::

::: mathlib
`Stream'.Seq.join_cons` · `Mathlib.Data.Seq.Basic`

`Stream'.Seq.join` concatenates a sequence of nonempty sequences. The lemmas `Stream'.Seq.join_nil`, `Stream'.Seq.join_cons` and `Stream'.Seq.join_append` are the equations of the text. On nonempty sequences, `Stream'.Seq1.ret` and `Stream'.Seq1.bind` form a monad, and `Stream'.Seq1.lawfulMonad` proves the monad laws.

<?decl Stream'.Seq.join_cons?>
:::

Common errors of a learner: The first error is to expect `Stream'.Seq.toList` to work on each sequence; it takes a proof of `Terminates`, and no algorithm can give that proof in general. The second error is to prove an equation of sequences by induction on the sequence; a sequence need not be finite, and the right tool is a bisimulation. The third error is to pass sequences with empty pieces to `Stream'.Seq.join`; the pieces have the type `Seq1 α`, which is nonempty by construction. The fourth error is to confuse `Stream'.Seq.head` with a total head; it returns an `Option`.

### Exercises

1. (A) Compute $\mathrm{take}\ 3\ (\mathrm{append}(\mathrm{ofList}[1])(\mathrm{ofList}[2, 3, 4]))$ and the length of $\mathrm{append}(\mathrm{ofList}[1])(\mathrm{ofList}[2, 3, 4])$. Hint: first show that the append equals $\mathrm{ofList}[1, 2, 3, 4]$ with the cons equations.
2. (A) Show that $\mathrm{map}\ g\ (\mathrm{cons}\ a\ s) = \mathrm{cons}(g\ a)(\mathrm{map}\ g\ s)$ by a comparison of entries. Hint: the entry at $0$ is $\mathrm{Option.map}\ g\ (\mathrm{some}\ a)$.
3. (A) Show that the tail of $\mathrm{nil}$ is $\mathrm{nil}$, and that $\mathrm{destruct}\ s = \mathrm{none}$ implies $s = \mathrm{nil}$. Hint: use the sequence condition and induction on the index.
4. (B) Prove $\mathrm{append}\ s\ \mathrm{nil} = s$ by a bisimulation. Hint: use the relation $s_1 = \mathrm{append}\ v\ \mathrm{nil}$, $s_2 = v$, and split on $v$.
5. (B) Prove that $\mathrm{map}\ g\ s$ terminates if and only if $s$ terminates, and that the lengths agree. Hint: $\mathrm{Option.map}\ g\ x = \mathrm{none}$ if and only if $x = \mathrm{none}$.
6. (B) Prove $\mathrm{map}\ g\ (\mathrm{append}\ s\ t) = \mathrm{append}(\mathrm{map}\ g\ s)(\mathrm{map}\ g\ t)$. Hint: the relation is "there are $s, t$ with $s_1 = \mathrm{map}\ g\ (\mathrm{append}\ s\ t)$ and $s_2 = \mathrm{append}(\mathrm{map}\ g\ s)(\mathrm{map}\ g\ t)$"; split on $s$ and then on $t$, as in the proof of associativity.
7. (C) For a sequence $S$ of sequences that can be empty, let $J\ S$ be the concatenation, when it exists. Show that the head of $J\ S$ is not determined by the first $N$ pieces of $S$ for any $N$. Hint: compare the sequence of $\mathrm{nil}$ pieces with the sequence that has $\mathrm{ofList}[0]$ at index $N$ and $\mathrm{nil}$ elsewhere.

### Notes and history

Sequences that can be finite or infinite are the greatest fixed point of the functor $X \mapsto 1 + \alpha \times X$. Lean has no native coinductive types, so Mathlib builds this type from streams of options and proves its principles by hand. Chapter 7 gives the general construction of such types from polynomial functors.

The Mathlib files are by these authors, read from their headers: `Mathlib.Data.Seq.Defs` by Mario Carneiro, and `Mathlib.Data.Seq.Basic` by Mario Carneiro and Vasilii Nesterov.

### Reference

<?reference?>
