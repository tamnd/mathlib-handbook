---
title: Tapes, configurations and machines
kind: theory
modules:
  - Mathlib.Computability.StateTransition
  - Mathlib.Computability.TuringMachine.Tape
  - Mathlib.Computability.TuringMachine.Config
  - Mathlib.Computability.TuringMachine.PostTuringMachine
  - Mathlib.Computability.TuringMachine.StackTuringMachine
explains:
  E3: [StateTransition.eval, StateTransition.Reaches, StateTransition.mem_eval, StateTransition.Respects, StateTransition.tr_eval, Turing.ListBlank, Turing.Tape, Turing.Tape.move, Turing.Tape.nth, Turing.TM0.Machine, Turing.TM0.step, Turing.TM0.eval, Turing.TM1.Stmt, Turing.TM1.step, Turing.TM2.Stmt, Turing.TM2.eval, Turing.TM0to1.tr_respects, Turing.TM1to0.tr_eval, Turing.TM2to1.tr_eval, Turing.ToPartrec.Code, Turing.ToPartrec.Code.eval, Turing.ToPartrec.stepNormal_eval]
  E2: [StateTransition.tr_eval_dom, StateTransition.EvalsTo, Turing.BlankRel, Turing.Tape.write, Turing.Tape.move_right_nth, Turing.TM0.Supports, Turing.TM1.stepAux, Turing.TM1to1.exists_enc_dec, Turing.TM1to1.tr_respects, Turing.TM2to1.addBottom, Turing.ToPartrec.Code.rfind, Turing.ToPartrec.Code.exists_code, Turing.ToPartrec.step]
  E1: auto
families: []
requires: [V01.C01, V03.C02, V32.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Tapes, configurations and machines

### Overview

A Turing machine has a finite set of states and reads and writes symbols on an unbounded tape, one cell at a time. Each step is clearly mechanical, and the model computes each partial recursive function. Chapter 6 defined computability by closure conditions on functions. This chapter gives the machine model and connects the two.

In Mathlib each machine model has a type of configurations and a step function to optional configurations, where `none` means that the machine halts. A run iterates the step function, and the result is the last configuration. A simulation is a relation between configurations that the step functions respect.

Mathlib defines three models: TM0, the classical machine; TM1, a machine with a small program language and a local store; and TM2, a machine with several stacks in place of a tape. Translations show that they compute the same functions. A last part gives a basis of partial recursive functions on lists of numbers with a sequential evaluator, which Section 2 compiles into TM2.

### Definitions

**Definition (State transition system).** A state transition system on a type $\sigma$ is a function $f : \sigma \to \mathrm{Option}\ \sigma$. The relation $\mathrm{Reaches}\ f$ is the reflexive transitive closure of the relation $b \in f(a)$, and $\mathrm{Reaches}_1\ f$ is the transitive closure. The evaluation $\mathrm{eval}\ f\ a$ is the partial value: the state $b$ with $\mathrm{Reaches}\ f\ a\ b$ and $f(b) = \mathrm{none}$, if such a $b$ exists.

Because $f$ is a function, there is at most one such $b$.

**Definition (Respects).** Let $f_1$ on $\sigma_1$ and $f_2$ on $\sigma_2$ be transition systems, and let $\mathrm{tr}$ be a relation between $\sigma_1$ and $\sigma_2$. Then $f_2$ respects $f_1$ along $\mathrm{tr}$ if, whenever $\mathrm{tr}(a_1, a_2)$:

1. if $f_1(a_1) = \mathrm{some}\ b_1$, there is $b_2$ with $\mathrm{tr}(b_1, b_2)$ and $\mathrm{Reaches}_1\ f_2\ a_2\ b_2$;
2. if $f_1(a_1) = \mathrm{none}$, then $f_2(a_2) = \mathrm{none}$.

**Definition (Tape).** Let $\Gamma$ be a type with a default element, the blank. A half-tape $\mathrm{ListBlank}\ \Gamma$ is the quotient of $\mathrm{List}\ \Gamma$ by the relation "one list is the other extended by blanks". A tape is a triple $(a, L, R)$ of a head symbol $a$ and two half-tapes. It represents the bi-infinite sequence $\dots, L_1, L_0, a, R_0, R_1, \dots$ with the head on $a$. Cell $i \in \mathbb{Z}$ is $\mathrm{nth}\ i$: cell $0$ is $a$, cell $n+1$ is $R_n$ and cell $-(n+1)$ is $L_n$.

So a half-tape is an infinite list with finitely many nonblank cells. The moves are $\mathrm{move}\ \mathrm{left}\ (a, L, R) = (L_0, L_{\ge 1}, a :: R)$ and $\mathrm{move}\ \mathrm{right}\ (a, L, R) = (R_0, a :: L, R_{\ge 1})$, and $\mathrm{write}\ b\ (a, L, R) = (b, L, R)$. The tape $\mathrm{mk}_1\ l$ puts $l$ from the head to the right.

**Definition (TM0 machine).** Let $\Gamma$ and $\Lambda$ be inhabited types; the default of $\Lambda$ is the start state. A statement is $\mathrm{move}\ d$ for a direction $d$ or $\mathrm{write}\ b$ for $b \in \Gamma$. A TM0 machine is a function $M : \Lambda \to \Gamma \to \mathrm{Option}(\Lambda \times \mathrm{Stmt})$. A configuration is a pair $(q, T)$ of a state and a tape. The step function reads the head symbol $a = T.\mathrm{head}$. If $M\ q\ a = \mathrm{none}$, the machine halts. If $M\ q\ a = \mathrm{some}(q', s)$, it performs $s$ on $T$ and goes to state $q'$.

The initial configuration on input $l$ is $(\mathrm{default}, \mathrm{mk}_1\ l)$, and $\mathrm{TM0.eval}\ M\ l$ is the right part of the tape, from the head on, in the final configuration. A set $S$ of states supports $M$ if it contains the start state and is closed under transitions.

**Definition (TM1 machine).** A TM1 machine has labels $\Lambda$, a local store $\sigma$ and a program $M : \Lambda \to \mathrm{Stmt}$. A statement is one of $\mathrm{move}\ d\ q$, $\mathrm{write}\ f\ q$, $\mathrm{load}\ f\ q$, $\mathrm{branch}\ p\ q_1\ q_2$, $\mathrm{goto}\ l$ and $\mathrm{halt}$. The functions $f$, $p$ and $l$ read the head symbol and the store. A configuration is an optional label, a store value and a tape. One step runs the body of the current label until a $\mathrm{goto}$ or a $\mathrm{halt}$.

The statements other than $\mathrm{goto}$ and $\mathrm{halt}$ take zero steps.

**Definition (TM2 machine).** A TM2 machine has a type $K$ of stack indices, an alphabet $\Gamma_k$ for each stack, labels, a store and a program. Its statements are $\mathrm{push}\ k\ f\ q$, $\mathrm{peek}\ k\ f\ q$, $\mathrm{pop}\ k\ f\ q$, $\mathrm{load}$, $\mathrm{branch}$, $\mathrm{goto}$ and $\mathrm{halt}$. A configuration is an optional label, a store value and a list for each stack; a stack has a definite end, which $\mathrm{pop}$ detects. On input $L$ on stack $k$, the other stacks start empty, and $\mathrm{TM2.eval}\ M\ k\ L$ is the final content of stack $k$.

**Definition (The list basis).** The type $\mathrm{Turing.ToPartrec.Code}$ has the constructors $\mathrm{zero'}$, $\mathrm{succ}$, $\mathrm{tail}$, $\mathrm{cons}$, $\mathrm{comp}$, $\mathrm{case}$ and $\mathrm{fix}$. Its semantics $\mathrm{eval} : \mathrm{Code} \to (\mathrm{List}\ \mathbb{N} \to \mathrm{Part}(\mathrm{List}\ \mathbb{N}))$ is:

1. $\mathrm{zero'}\ v = 0 :: v$, $\mathrm{succ}\ v = [h + 1]$ and $\mathrm{tail}\ v = v_{\ge 1}$, where $h$ is the head of $v$, or $0$ for the empty list;
2. $\mathrm{cons}\ f\ g\ v = \mathrm{head}(f\ v) :: g\ v$ and $\mathrm{comp}\ f\ g\ v = f(g\ v)$;
3. $\mathrm{case}\ f\ g$ applies $f$ to the tail if the head is $0$ and applies $g$ to $n :: \mathrm{tail}$ if the head is $n + 1$;
4. $\mathrm{fix}\ f\ v$ computes $w = f\ v$; if the head of $w$ is $0$ it returns the tail of $w$, and otherwise it continues with $\mathrm{fix}\ f$ on the tail of $w$.

A continuation $k$ is a code with a hole. A configuration is $\mathrm{halt}\ v$ or $\mathrm{ret}\ k\ v$, and $\mathrm{stepNormal}\ c\ k\ v$ descends into $c$ to a basic operation.

### Theorems and proofs

**Theorem (Simulation preserves evaluation).** Let $f_2$ respect $f_1$ along $\mathrm{tr}$, and let $\mathrm{tr}(a_1, a_2)$. If $b_1 \in \mathrm{eval}\ f_1\ a_1$, there is $b_2$ with $\mathrm{tr}(b_1, b_2)$ and $b_2 \in \mathrm{eval}\ f_2\ a_2$.

*Proof.* First, $b \in \mathrm{eval}\ f\ a$ holds if and only if $\mathrm{Reaches}\ f\ a\ b$ and $f(b) = \mathrm{none}$. So $\mathrm{Reaches}\ f_1\ a_1\ b_1$ and $f_1(b_1) = \mathrm{none}$. Next, prove by induction on the path from $a_1$ to $c_1$ that there is $c_2$ with $\mathrm{tr}(c_1, c_2)$ and $\mathrm{Reaches}\ f_2\ a_2\ c_2$. For the empty path, take $c_2 = a_2$. For a path that ends with a step $c_1' \in f_1(c_1)$, the induction gives $c_2$ for $c_1$. Condition 1 gives $c_2'$ with $\mathrm{tr}(c_1', c_2')$ and $\mathrm{Reaches}_1\ f_2\ c_2\ c_2'$. Join the two paths. Apply this to $b_1$ and get $b_2$. Condition 2 at $b_1$ gives $f_2(b_2) = \mathrm{none}$. So $b_2 \in \mathrm{eval}\ f_2\ a_2$. $\square$

The domains of the two evaluations are also equal; Exercise 7 asks for the proof.

**Proposition (Tape moves).** For each tape $T$ and $i \in \mathbb{Z}$: $(\mathrm{move\ right}\ T).\mathrm{nth}\ i = T.\mathrm{nth}(i + 1)$, $(\mathrm{move\ left}\ T).\mathrm{nth}\ i = T.\mathrm{nth}(i - 1)$, and the two moves are inverse. Also $(\mathrm{write}\ b\ T).\mathrm{nth}\ i$ is $b$ if $i = 0$ and $T.\mathrm{nth}\ i$ otherwise.

*Proof.* Let $T = (a, L, R)$ and $T' = \mathrm{move\ left}\ T = (L_0, L_{\ge 1}, a :: R)$. Then $T'.\mathrm{nth}\ 0 = L_0 = T.\mathrm{nth}(-1)$. For $n \ge 0$, $T'.\mathrm{nth}(n + 1) = (a :: R)_n$, which is $a = T.\mathrm{nth}\ 0$ for $n = 0$ and $R_{n-1} = T.\mathrm{nth}\ n$ for $n \ge 1$. Also $T'.\mathrm{nth}(-(n+1)) = L_{n+1} = T.\mathrm{nth}(-(n+2))$. These are the three cases of the left formula. For the inverse, $\mathrm{move\ right}\ T' = ((a::R)_0, L_0 :: L_{\ge 1}, R) = (a, L, R)$. The identity $L_0 :: L_{\ge 1} = L$ holds in the quotient also for $L$ blank, because the head of a blank half-tape is the blank and its tail is blank. The right formula follows from the left one and the inverse law. The write formula holds by definition. $\square$

**Theorem (TM0 and TM1 simulate each other).** For each TM0 machine $M$ there is a TM1 machine whose step function respects $\mathrm{TM0.step}\ M$. For each TM1 machine $M$ there is a TM0 machine $M'$ with $\mathrm{TM0.eval}\ M'\ l = \mathrm{TM1.eval}\ M\ l$ for all $l$.

*Proof.* From TM0 to TM1: use labels $\mathrm{normal}\ q$ and $\mathrm{act}\ s\ q$. The body of $\mathrm{normal}\ q$ halts if $M\ q\ a = \mathrm{none}$ for the head $a$, and jumps to $\mathrm{act}\ s\ q'$ if $M\ q\ a = \mathrm{some}(q', s)$. The body of $\mathrm{act}\ s\ q'$ performs $s$ and jumps to $\mathrm{normal}\ q'$. Translate a TM0 configuration $(q, T)$ to the TM1 configuration with label $\mathrm{normal}\ q$ if $M\ q\ T.\mathrm{head}$ is defined and with no label otherwise. A TM0 step from $(q, T)$ is matched by two TM1 steps, and by a third step to the halting label if $M$ halts in the new configuration.

From TM1 to TM0: take the states of $M'$ to be pairs of an optional TM1 statement and a store value. In state $(\mathrm{some}\ q, v)$ with head $a$, the TM0 machine passes through the $\mathrm{load}$ and $\mathrm{branch}$ parts of $q$ and stops at the first $\mathrm{move}$, $\mathrm{write}$, $\mathrm{goto}$ or $\mathrm{halt}$. A $\mathrm{move}$ or $\mathrm{write}$ becomes one TM0 action, and the new state holds the rest of $q$. A $\mathrm{goto}\ l$ becomes the dummy action "write $a$" with the new state $(\mathrm{some}(M(l\ a\ v)), v)$, and $\mathrm{halt}$ becomes "write $a$" with the state $(\mathrm{none}, v)$, where the TM0 machine halts. Each TM1 step becomes one or more TM0 steps, so the relation "replace the label by its body" is respected, and the simulation theorem gives the equality. $\square$

**Theorem (Binary alphabet).** For a finite alphabet $\Gamma$ there are $n$ and maps $\mathrm{enc} : \Gamma \to \mathrm{Bool}^n$, $\mathrm{dec} : \mathrm{Bool}^n \to \Gamma$ with $\mathrm{dec} \circ \mathrm{enc} = \mathrm{id}$ and $\mathrm{enc}(\mathrm{blank}) = (\mathrm{false}, \dots, \mathrm{false})$. Each TM1 machine over $\Gamma$ is simulated by a TM1 machine over $\mathrm{Bool}$.

*Proof.* Take a bijection $\Gamma \cong \mathrm{Fin}\ m$ that sends the blank to $0$, and $n$ with $2^n \ge m$. The new machine stores each symbol as a block of $n$ cells. It reads a symbol by $n$ branches over the block, moves by $n$ cells, and writes by a jump to a label that writes the $n$ bits and returns. Because blank maps to blanks, the blank parts of the tapes correspond. $\square$

**Theorem (Stacks on one tape).** Each TM2 machine $M$ with finitely many stacks is simulated by a TM1 machine, and the output stack of $M$ can be read off from the final tape.

*Proof.* Use the alphabet $\mathrm{Bool} \times \prod_k \mathrm{Option}\ \Gamma_k$. The first component marks the bottom cell, where the machine rests. Component $k$ of the cells right of the bottom holds stack $k$, with the top at the far end and $\mathrm{none}$ above it. A $\mathrm{push}$, $\mathrm{pop}$ or $\mathrm{peek}$ on stack $k$ walks to the end of stack $k$, acts there and walks back. Each TM2 step becomes finitely many TM1 steps, and the relation "the tape encodes the stacks" is respected. $\square$

**Theorem (Sequential evaluation of the list basis).** For each code $c$ and list $v$, $\mathrm{eval}\ \mathrm{step}\ (\mathrm{stepNormal}\ c\ \mathrm{halt}\ v) = \mathrm{halt} \mathbin{\langle\$\rangle} \mathrm{eval}\ c\ v$.

*Proof sketch.* Call $c$ correct if, for all $k$ and $v$, running $\mathrm{stepNormal}\ c\ k\ v$ gives the same result as running $\mathrm{ret}\ k\ w$ for $w \in \mathrm{eval}\ c\ v$. Prove that each code is correct by induction on $c$. The basic codes take one step. For $\mathrm{cons}$, $\mathrm{comp}$ and $\mathrm{case}$, use the parts, since the continuation records the remaining work. For $\mathrm{fix}\ f$, induct along the fixed point: each round evaluates $f$ in the continuation $\mathrm{fix}\ f\ k$, which returns the tail or starts the next round. Then take $k = \mathrm{halt}$. $\square$

### Examples

**Example (A machine that adds one).** Write numbers in binary with the least significant bit first: $11 = 1 + 2 + 8$ is $[1, 1, 0, 1]$. Let $\Gamma = \{\sqcup, 0, 1\}$ with blank $\sqcup$, and let the states be $A, B, C, D$ with start $A$. The machine is:

1. $A$ on $1$: write $0$, go to $B$. $B$ on any symbol: move right, go to $A$.
2. $A$ on $0$ or $\sqcup$: write $1$, go to $C$.
3. $C$ on $0$ or $1$: move left, stay in $C$. $C$ on $\sqcup$: move right, go to $D$.
4. $D$: halt, that is, $M\ D\ a = \mathrm{none}$ for each $a$.

On input $[1,1,0,1]$, the head starts at cell $0$. Steps 1 to 4 turn cells $0$ and $1$ to $0$ and move the head to cell $2$. Step 5 writes $1$ at cell $2$. Steps 6, 7 and 8 move left from cell $2$ to cell $-1$, which holds $\sqcup$. Step 9 moves right to cell $0$ in state $D$, and the machine halts. The output is $[0, 0, 1, 1]$, that is $4 + 8 = 12$.

**Proposition (Correctness of the machine).** Let $l$ be a list of bits whose first $k$ entries are $1$ and whose entry $k$ is $0$ or absent. The machine halts after $3k + 3$ steps with the head at cell $0$, and the output is the binary form of $N + 1$, where $N$ is the value of $l$.

*Proof.* By induction on $j \le k$, after $2j$ steps the machine is in state $A$ at cell $j$, and cells $0$ to $j - 1$ hold $0$: each round is "write $0$" and "move right". At cell $k$, the symbol is $0$ or $\sqcup$, so step $2k + 1$ writes $1$ there. Then $C$ moves left $k + 1$ times, through cells $k, k-1, \dots, 0$, to cell $-1$. Cells $0$ to $k$ are nonblank and cell $-1$ is blank, since the input starts at cell $0$. One more step moves right to cell $0$ in state $D$. The total is $2k + 1 + (k + 1) + 1 = 3k + 3$. For the value, $N = (2^k - 1) + 2^k b_k + \sum_{i > k} 2^i b_i$ with $b_k = 0$. The new tape has value $2^k + \sum_{i > k} 2^i b_i = N + 1$. $\square$

For $l = []$, which represents $0$, $k = 0$ and the run takes $3$ steps with output $[1]$. For $l = [1, 1]$, which represents $3$, it takes $9$ steps with output $[0, 0, 1]$.

**Example (The list basis).** $\mathrm{eval}\ (\mathrm{comp}\ \mathrm{succ}\ \mathrm{succ})\ [4, 7] = [6]$. The code $\mathrm{comp}\ \mathrm{tail}\ \mathrm{zero'}$ is the identity: it maps $v$ to $0 :: v$ and then to $v$. The code $\mathrm{rfind}\ f = \mathrm{comp}\ \mathrm{pred}\ (\mathrm{comp}\ (\mathrm{fix}(\mathrm{cons}\ f\ (\mathrm{cons}\ \mathrm{succ}\ \mathrm{tail})))\ \mathrm{zero'})$ starts from $0 :: v$. Each round maps $n :: v$ to $f(n :: v)_0 :: (n + 1) :: v$. The loop stops at the first $n$ with $f(n :: v)_0 = 0$ and leaves $(n + 1) :: v$, and $\mathrm{pred}$ returns $[n]$.

### The library around it

::: mathlib
`StateTransition.tr_eval` · `Mathlib.Computability.StateTransition`

`StateTransition.mem_eval` states `b ∈ eval f a ↔ Reaches f a b ∧ f b = none`. `StateTransition.tr_eval` is the simulation theorem and `StateTransition.tr_eval_dom` the equality of domains. `StateTransition.EvalsTo` records a run with its number of steps; Section 2 uses it for time bounds.

<?decl StateTransition.tr_eval?>
:::

::: mathlib
`Turing.Tape` · `Mathlib.Computability.TuringMachine.Tape`

`Turing.ListBlank Γ` is the quotient of lists by `Turing.BlankRel`. `Turing.Tape` has the fields `head`, `left` and `right`, and `Turing.Tape.move`, `Turing.Tape.write` and `Turing.Tape.nth` are the operations of the text, with `Turing.Tape.move_right_nth`.

<?decl Turing.Tape?>
:::

::: mathlib
`Turing.TM1to0.tr_eval` · `Mathlib.Computability.TuringMachine.PostTuringMachine`

`Turing.TM0.Machine Γ Λ` is `Λ → Γ → Option (Λ × Turing.TM0.Stmt Γ)`. `Turing.TM0to1.tr_respects`, `Turing.TM1to0.tr_eval` and `Turing.TM1to1.tr_respects` are the translations, and `Turing.TM1to1.exists_enc_dec` gives the binary code of a finite alphabet.

<?decl Turing.TM1to0.tr_eval?>
:::

::: mathlib
`Turing.TM2to1.tr_eval` · `Mathlib.Computability.TuringMachine.StackTuringMachine`

`Turing.TM2.eval M k L` returns stack `k`. `Turing.TM2to1.addBottom` marks the bottom cell, and `Turing.TM2to1.tr_eval` relates the final tape of the TM1 machine to the final stacks of the TM2 machine.

<?decl Turing.TM2to1.tr_eval?>
:::

::: mathlib
`Turing.ToPartrec.stepNormal_eval` · `Mathlib.Computability.TuringMachine.Config`

`Turing.ToPartrec.Code.exists_code` gives a code in the list basis for each `Nat.Partrec'` function on vectors, with `Turing.ToPartrec.Code.rfind` for search. `Turing.ToPartrec.step` is the sequential evaluator, and `Turing.ToPartrec.stepNormal_eval` is the theorem of the text.

<?decl Turing.ToPartrec.stepNormal_eval?>
:::

Common errors of a learner: The first error is to count a TM1 `move` or `write` as a step; only `goto` and `halt` take a step. The second error is to expect `Turing.TM0.eval` to return a list; it returns a `ListBlank`, with an unknown number of blanks at the end. The third error is to forget that the start state is the `default` of `Λ`. The fourth error is to confuse `Turing.ToPartrec.Code` with `Nat.Partrec.Code`; the first acts on lists of numbers, the second on single numbers.

### Exercises

1. (A) Run the add-one machine on $[0, 1]$, which represents $2$. List the configurations and check that the run takes $3$ steps with output $[1, 1]$. Hint: $k = 0$.
2. (A) Prove that $\mathrm{Reaches}\ f\ a\ b$ and $b \in \mathrm{eval}\ f\ a$ imply $\mathrm{Reaches}\ f\ b\ c \iff c = b$. Hint: $f(b) = \mathrm{none}$.
3. (A) Show that $\mathrm{comp}\ \mathrm{tail}\ \mathrm{succ}$ maps each list to $[]$, and compute $\mathrm{eval}\ (\mathrm{cons}\ \mathrm{succ}\ \mathrm{tail})\ [3, 5, 8]$. Hint: the answer is $[4, 5, 8]$.
4. (B) Design a TM0 machine over $\{\sqcup, 1\}$ that doubles a number in unary: input $1^n$, output $1^{2n}$. Hint: mark a $1$, carry a copy to the right end, and return.
5. (B) Design a TM0 machine that subtracts one from a positive binary number, least significant bit first. Hint: swap $0$ and $1$ in the add-one machine.
6. (B) Write a TM2 program with two stacks that reverses its input stack. Hint: the output must be on the input stack; moving a whole stack onto another one reverses it, so use three stacks and move from stack $1$ to $2$, from $2$ to $3$ and from $3$ to $1$.
7. (C) Prove that if $f_2$ respects $f_1$ along $\mathrm{tr}$ and $\mathrm{tr}(a_1, a_2)$, then $\mathrm{eval}\ f_1\ a_1$ is defined if and only if $\mathrm{eval}\ f_2\ a_2$ is defined. Hint: for the hard direction, show that an infinite run of $f_1$ gives runs of $f_2$ from $a_2$ of each length.

### Notes and history

Turing introduced his machines in 1936, and Post gave a similar model in the same year. The TM1 model follows the program-like B-machines of Wang. Multi-stack and multi-tape variants are standard in complexity theory, where the cost of a simulation matters.

The Mathlib authors, from the file headers: `Mathlib.Computability.StateTransition` by Mario Carneiro, Pim Spelier and Daan van Gent; `Mathlib.Computability.TuringMachine.Tape`, `Mathlib.Computability.TuringMachine.Config`, `Mathlib.Computability.TuringMachine.PostTuringMachine` and `Mathlib.Computability.TuringMachine.StackTuringMachine` by Mario Carneiro.

### Reference

<?reference?>
