---
title: Turing computability and partial recursion
kind: theory
modules:
  - Mathlib.Computability.Encoding
  - Mathlib.Computability.TuringMachine.Computable
  - Mathlib.Computability.TuringMachine.ToPartrec
explains:
  E3: [Computability.Encoding, Computability.Encoding.encode_injective, Computability.Encoding.card_le_aleph0, Computability.encodeNat, Computability.encodingNatBool, Computability.encodingProd, Turing.FinTM2, Turing.TM2Outputs, Turing.TM2Computable, Turing.TM2ComputableInTime, Turing.TM2ComputableInPolyTime, Turing.idComputableInPolyTime, Turing.PartrecToTM2.tr, Turing.PartrecToTM2.trList, Turing.PartrecToTM2.tr_respects, Turing.PartrecToTM2.tr_eval, Turing.PartrecToTM2.tr_supports]
  E2: [Computability.Γ', Computability.encodePosNum, Computability.decodeNat, Computability.encodingNatΓ', Computability.unaryEncodingNat, Computability.encodingBoolBool, Computability.encodingList, Computability.Encoding.card_le_card_list, Turing.FinTM2.step, Turing.initList, Turing.haltList, Turing.TM2OutputsInTime, Turing.TM2ComputableAux, Turing.TM2ComputableInPolyTime.toTM2ComputableInTime, Turing.TM2ComputableInTime.toTM2Computable, Turing.idComputer, Turing.idComputable, Turing.PartrecToTM2.Γ', Turing.PartrecToTM2.K', Turing.PartrecToTM2.Λ', Turing.PartrecToTM2.trNat, Turing.PartrecToTM2.trLList, Turing.PartrecToTM2.trNormal, Turing.PartrecToTM2.TrCfg, Turing.PartrecToTM2.init, Turing.PartrecToTM2.succ_ok, Turing.PartrecToTM2.codeSupp]
  E1: auto
families: []
requires: [V01.C01, V02.C01, V03.C08, V32.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Turing computability and partial recursion

### Overview

A Turing machine works on symbols, and a function of mathematics works on numbers, lists or pairs. To say that a machine computes a function, one fixes an encoding of the inputs and outputs as words over a finite alphabet. The machine then computes the function if it turns the code of each input into the code of the output.

Mathlib defines encodings in the file `Encoding.lean`, and Turing computability, with and without time bounds, in `Computable.lean`. The model of computation is a bundled TM2 machine with finitely many stacks, labels and store values. Time is the number of steps. The definitions prepare the complexity class P: a function is computable in polynomial time if a machine computes it within a number of steps bounded by a polynomial in the length of the input code.

The file `ToPartrec.lean` proves the other half of the classical equivalence. It compiles each code of the list basis of the previous section into a TM2 machine with four stacks, and proves that the machine halts exactly when the code is defined, with the right output. Together with the theorem that each partial recursive function has a code, this shows that each partial recursive function is computed by a Turing machine.

### Definitions

**Definition (Encoding).** Let $\alpha$ be a type and $\Gamma$ an alphabet. An encoding of $\alpha$ in $\Gamma$ consists of $\mathrm{encode} : \alpha \to \mathrm{List}\ \Gamma$ and $\mathrm{decode} : \mathrm{List}\ \Gamma \to \mathrm{Option}\ \alpha$ with $\mathrm{decode}(\mathrm{encode}\ x) = \mathrm{some}\ x$ for all $x$.

The decoder need not reject the words that are not codes; it only has to invert the encoder on codes.

**Definition (Binary and unary codes of numbers).** The binary code $\mathrm{encodeNat}\ n$ is the list of bits of $n$, least significant bit first, with no trailing zero: $\mathrm{encodeNat}\ 0 = []$, and for $n > 0$, the code of $2n$ is $\mathrm{false} :: \mathrm{encodeNat}\ n$ and the code of $2n + 1$ is $\mathrm{true} :: \mathrm{encodeNat}\ n$. The unary code of $n$ is $n$ copies of $\mathrm{true}$, and the unary decoder is the length.

In Mathlib the binary code goes through the type $\mathrm{PosNum}$ of positive binary numbers, built from $\mathrm{one}$, $\mathrm{bit0}$ and $\mathrm{bit1}$. The alphabet $\Gamma'$ has the symbols $\mathrm{blank}$, $\mathrm{bit}\ b$, $\mathrm{bra}$, $\mathrm{ket}$ and $\mathrm{comma}$, and $\mathrm{encodingNat}\Gamma'$ is the binary code with each bit $b$ written as $\mathrm{bit}\ b$.

**Definition (Product encoding).** Given encodings of $\alpha$ in $\Gamma_1$ and of $\beta$ in $\Gamma_2$, the encoding of $\alpha \times \beta$ in $\Gamma_1 \oplus \Gamma_2$ maps $(x, y)$ to the code of $x$ with each symbol tagged $\mathrm{inl}$, followed by the code of $y$ with each symbol tagged $\mathrm{inr}$. The decoder keeps the $\mathrm{inl}$ symbols for $x$ and the $\mathrm{inr}$ symbols for $y$.

**Definition (Bundled TM2 machine).** A bundled machine $\mathrm{tm}$ has a finite type $K$ of stacks with decidable equality, an input stack $k_0$ and an output stack $k_1$, alphabets $\Gamma_k$, a finite type of labels with a main label, a finite store type with an initial value, a finite input alphabet $\Gamma_{k_0}$, and a program $m$ in the TM2 language. The initial configuration on a word $s$ has the main label, the initial store, $s$ on stack $k_0$ and all other stacks empty. The halting configuration with output $s$ has no label, the initial store, $s$ on stack $k_1$ and all other stacks empty.

**Definition (Outputs).** $\mathrm{TM2Outputs}\ \mathrm{tm}\ l\ l'$ is a run of the step function from the initial configuration on $l$ to the halting configuration with output $l'$, with its number of steps. $\mathrm{TM2OutputsInTime}\ \mathrm{tm}\ l\ l'\ m$ adds the bound "at most $m$ steps".

**Definition (Turing computable function).** Let $e_a : \alpha \to \mathrm{List}\ \Gamma_a$ and $e_b : \beta \to \mathrm{List}\ \Gamma_b$ be encoding functions. A function $f : \alpha \to \beta$ is Turing computable if there are a bundled machine $\mathrm{tm}$, bijections of its input alphabet with $\Gamma_a$ and of its output alphabet with $\Gamma_b$, and for each $a$ a run that outputs the code of $f(a)$ from the code of $a$. It is computable in time $t : \mathbb{N} \to \mathbb{N}$ if each run takes at most $t(|e_a(a)|)$ steps, and in polynomial time if $t$ is a polynomial with coefficients in $\mathbb{N}$.

Mathlib states these as structures, not as propositions: a term of $\mathrm{TM2Computable}\ e_a\ e_b\ f$ contains the machine and the runs. Time counts calls of the step function. A TM2 step runs a finite statement, which may contain several stack operations, so the count agrees with the count of basic operations up to a constant factor that depends on the machine.

**Definition (The compiler of the list basis).** The machine $\mathrm{PartrecToTM2.tr}$ has four stacks: $\mathrm{main}$, $\mathrm{rev}$, $\mathrm{aux}$ and $\mathrm{stack}$. All four use the alphabet $\{\mathrm{cons}_l, \mathrm{cons}, \mathrm{bit0}, \mathrm{bit1}\}$, and the store holds the last popped symbol. A number is written in binary, least significant bit first, a list of numbers puts $\mathrm{cons}$ after each number, and a list of lists puts $\mathrm{cons}_l$ after each list. Each code $c$ and continuation give a label $\mathrm{trNormal}\ c\ k$, and $\mathrm{init}\ c\ v$ is the configuration at this label with $\mathrm{trList}\ v$ on $\mathrm{main}$.

In normal mode, $\mathrm{main}$ holds the input of the current code, and $\mathrm{stack}$ holds the data of the continuation. The stacks $\mathrm{rev}$ and $\mathrm{aux}$ are scratch space for moving and swapping lists. The labels form an infinite type, since they contain codes, but the evaluation of one code visits only finitely many labels.

### Theorems and proofs

**Proposition (Encodings are injective).** The encoding function of each encoding is injective. If $\Gamma$ is countable, a type with an encoding in $\Gamma$ is countable.

*Proof.* If $\mathrm{encode}\ x = \mathrm{encode}\ y$, then $\mathrm{some}\ x = \mathrm{decode}(\mathrm{encode}\ x) = \mathrm{decode}(\mathrm{encode}\ y) = \mathrm{some}\ y$, and $x = y$. For the second claim, $\mathrm{List}\ \Gamma$ is countable when $\Gamma$ is countable, since it is the countable union of the countable sets $\Gamma^n$. An injection into a countable type gives a countable domain. $\square$

So the type $\mathbb{N} \to \mathrm{Bool}$ has no encoding over a finite alphabet: by Cantor's theorem it is uncountable. A machine can only work on objects with finite descriptions.

**Proposition (Correctness of the binary code).** For each $n$, $\mathrm{decodeNat}(\mathrm{encodeNat}\ n) = n$.

*Proof.* For $n = 0$, the code is $[]$, and the decoder maps $[]$ to $0$. For $n > 0$, write $n$ as a positive binary number $p$ and prove $\mathrm{decodePosNum}(\mathrm{encodePosNum}\ p) = p$ by induction on $p$. For $p = \mathrm{one}$, the code is $[\mathrm{true}]$, and the decoder maps $\mathrm{true} :: []$ to $\mathrm{one}$. For $p = \mathrm{bit0}\ q$, the code is $\mathrm{false} :: \mathrm{code}(q)$, and the decoder maps $\mathrm{false} :: l$ to $\mathrm{bit0}$ of the decoding of $l$, which is $q$ by induction. For $p = \mathrm{bit1}\ q$, the code is $\mathrm{true} :: \mathrm{code}(q)$, and $\mathrm{code}(q)$ is nonempty. The decoder maps $\mathrm{true} :: l$ with $l \ne []$ to $\mathrm{bit1}$ of the decoding of $l$, which is $q$. Finally, a nonempty code decodes as a positive number, and the casts between $\mathrm{PosNum}$, $\mathrm{Num}$ and $\mathbb{N}$ are inverse. $\square$

**Proposition (Time bounds).** A computation in polynomial time is a computation in time $t(n) = p(n)$, and a computation in some time is a computation. The identity function on each type with an encoding over a finite alphabet is computable in polynomial time, with the constant polynomial $1$.

*Proof.* The first two claims forget data: the evaluation of the polynomial is a time function, and a run within a bound is a run. For the identity, take the machine with one stack, which is both the input and the output stack, one label, one store value, and the program $m = \mathrm{halt}$. From the initial configuration on $s$, one step executes $\mathrm{halt}$. It removes the label, keeps the store and leaves $s$ on the stack. This is the halting configuration with output $s$. So the run has $1$ step, and $1 \le p(|s|)$ for the constant polynomial $p = 1$. $\square$

**Theorem (Simulation of the list basis).** The machine $\mathrm{PartrecToTM2.tr}$ respects the step function of the sequential evaluator of the list basis, along the relation $\mathrm{TrCfg}$. For each code $c$ and list $v$,
$$\mathrm{eval}\ (\mathrm{TM2.step}\ \mathrm{tr})\ (\mathrm{init}\ c\ v) = \mathrm{halt} \mathbin{\langle\$\rangle} \mathrm{eval}\ c\ v,$$
where $\mathrm{halt}\ w$ is the halting configuration with $\mathrm{trList}\ w$ on $\mathrm{main}$ and the other stacks empty. The set $\mathrm{codeSupp}\ c\ k$ of labels is finite and supports the machine started at $\mathrm{trNormal}\ c\ k$.

*Proof sketch.* The relation $\mathrm{TrCfg}$ relates $\mathrm{ret}\ k\ v$ to the configuration at the label $\mathrm{ret}(k')$, where $k'$ is $k$ without its data, with $\mathrm{trList}\ v$ on $\mathrm{main}$, the data of $k$ on $\mathrm{stack}$, and the scratch stacks empty. It relates $\mathrm{halt}\ v$ to the halting configuration. Each subroutine has a correctness lemma. For example, $\mathrm{succ}$ turns $\mathrm{trList}[n]$ into $\mathrm{trList}[n+1]$, and $\mathrm{pred}$ performs the case split of $\mathrm{case}$. The subroutines for moving and copying lists keep the encodings in the right order with the help of $\mathrm{rev}$ and $\mathrm{aux}$. For each continuation, one step of the evaluator is a finite run of these subroutines, which ends in a related configuration. This proves the respect condition. The initial configuration $\mathrm{init}\ c\ v$ reaches a configuration related to $\mathrm{stepNormal}\ c\ \mathrm{halt}\ v$. The simulation theorem of Section 1 and the sequential evaluation theorem then give the equation. For the support, $\mathrm{codeSupp}$ collects the labels of the subroutines that the compilation of $c$ and of each part of $k$ uses, and the program only jumps between them. $\square$

**Corollary (Partial recursive functions are Turing computable).** Let $f : \mathbb{N}^n \to \mathrm{Part}\ \mathbb{N}$ be partial recursive. There is a code $c$ of the list basis such that, for each vector $v$, the machine $\mathrm{tr}$ started at $\mathrm{init}\ c\ v$ halts if and only if $f(v)$ is defined, and then $\mathrm{main}$ holds $\mathrm{trList}[f(v)]$. The machine uses only finitely many labels.

*Proof.* By the equivalence of bases in Chapter 6, $f$ is in $\mathrm{Nat.Partrec'}$. The code theorem of Section 1 gives $c$ with $\mathrm{eval}\ c\ v = \mathrm{pure} \mathbin{\langle\$\rangle} f(v)$, that is, $\mathrm{eval}\ c\ v$ is defined exactly when $f(v)$ is, with value $[f(v)]$. The simulation theorem gives the halting behaviour and the output. The support theorem with $k = \mathrm{halt}$ gives the finite set of labels. $\square$

The index of this edition has no declaration that packages the corollary as a term of $\mathrm{TM2Computable}$, and none for the converse statement that each Turing computable function is partial recursive. The converse holds classically: a configuration is a finite object, the step function is primitive recursive on codes of configurations, and the output is the result of an unbounded search for a halting step.

### Examples

**Example (Binary codes).** $6 = \mathrm{bit0}(\mathrm{bit1}\ \mathrm{one})$, so $\mathrm{encodeNat}\ 6 = [\mathrm{false}, \mathrm{true}, \mathrm{true}]$. $11 = \mathrm{bit1}(\mathrm{bit1}(\mathrm{bit0}\ \mathrm{one}))$, so $\mathrm{encodeNat}\ 11 = [\mathrm{true}, \mathrm{true}, \mathrm{false}, \mathrm{true}]$. This is the input of the add-one machine of Section 1. The unary code of $3$ is $[\mathrm{true}, \mathrm{true}, \mathrm{true}]$, and its binary code is $[\mathrm{true}, \mathrm{true}]$.

**Example (A pair).** With the binary code of $\mathbb{N}$ and the code $b \mapsto [b]$ of $\mathrm{Bool}$, the pair $(2, \mathrm{true})$ has the code $[\mathrm{inl}\ \mathrm{false}, \mathrm{inl}\ \mathrm{true}, \mathrm{inr}\ \mathrm{true}]$. The decoder reads $[\mathrm{false}, \mathrm{true}]$ from the $\mathrm{inl}$ symbols, which is $2$, and $[\mathrm{true}]$ from the $\mathrm{inr}$ symbols.

**Example (Stack contents of the compiler).** $\mathrm{trList}[1, 2] = [\mathrm{bit1}, \mathrm{cons}, \mathrm{bit0}, \mathrm{bit1}, \mathrm{cons}]$, since $1$ is $[\mathrm{bit1}]$ and $2$ is $[\mathrm{bit0}, \mathrm{bit1}]$. The number $0$ is the empty word, so $\mathrm{trList}[0, 0] = [\mathrm{cons}, \mathrm{cons}]$. For lists of lists, $\mathrm{trLList}[[], [1, 2]] = [\mathrm{cons}_l, \mathrm{bit1}, \mathrm{cons}, \mathrm{bit0}, \mathrm{bit1}, \mathrm{cons}, \mathrm{cons}_l]$.

**Example (The successor subroutine).** The subroutine $\mathrm{succ}$ pops symbols from $\mathrm{main}$. For each $\mathrm{bit1}$ it pushes $\mathrm{bit0}$ to $\mathrm{rev}$. At the first $\mathrm{bit0}$ it pushes $\mathrm{bit1}$ to $\mathrm{main}$. At a $\mathrm{cons}$ it pushes $\mathrm{cons}$ and then $\mathrm{bit1}$ to $\mathrm{main}$. Then it moves $\mathrm{rev}$ back to $\mathrm{main}$. On $\mathrm{trList}[3] = [\mathrm{bit1}, \mathrm{bit1}, \mathrm{cons}]$ it pops two $\mathrm{bit1}$, pushes two $\mathrm{bit0}$ to $\mathrm{rev}$, pops $\mathrm{cons}$, pushes $\mathrm{cons}$ and $\mathrm{bit1}$, and moves back. The result is $[\mathrm{bit0}, \mathrm{bit0}, \mathrm{bit1}, \mathrm{cons}] = \mathrm{trList}[4]$. This is the add-one machine of Section 1, with the stack $\mathrm{rev}$ in place of the movement of the head.

### The library around it

::: mathlib
`Computability.Encoding` · `Mathlib.Computability.Encoding`

`Computability.Encoding α Γ` has the fields `encode`, `decode` and `decode_encode`. `Computability.encodingNatBool`, `Computability.encodingNatΓ'`, `Computability.unaryEncodingNat`, `Computability.encodingBoolBool`, `Computability.encodingList` and `Computability.encodingProd` are the encodings of the text. `Computability.Encoding.card_le_aleph0` is the countability bound. The older name `FinEncoding` is deprecated; use `Encoding α Γ` with `[Fintype Γ]`.

<?decl Computability.Encoding?>
:::

::: mathlib
`Turing.TM2ComputableInPolyTime` · `Mathlib.Computability.TuringMachine.Computable`

`Turing.FinTM2` is the bundled machine, with `Turing.initList` and `Turing.haltList`. `Turing.TM2Outputs` is an `EvalsTo` run of `Turing.FinTM2.step`. `Turing.TM2Computable`, `Turing.TM2ComputableInTime` and `Turing.TM2ComputableInPolyTime` take encoding functions `α → List Γ`, not bundled encodings, and the time polynomial is a `Polynomial ℕ`. `Turing.idComputableInPolyTime` is the identity example.

<?decl Turing.TM2ComputableInPolyTime?>
:::

::: mathlib
`Turing.PartrecToTM2.tr_eval` · `Mathlib.Computability.TuringMachine.ToPartrec`

`Turing.PartrecToTM2.tr` is the program, with labels in `Turing.PartrecToTM2.Λ'`, stacks indexed by `Turing.PartrecToTM2.K'` and symbols in `Turing.PartrecToTM2.Γ'`. `Turing.PartrecToTM2.trList` and `Turing.PartrecToTM2.trLList` are the stack encodings, `Turing.PartrecToTM2.tr_respects` is the respect condition, `Turing.PartrecToTM2.tr_eval` is the main equation, and `Turing.PartrecToTM2.tr_supports` gives finite support by `Turing.PartrecToTM2.codeSupp`.

<?decl Turing.PartrecToTM2.tr_eval?>
:::

Common errors of a learner: The first error is to expect `Turing.TM2Computable` to be a proposition; it is a structure, and the proposition is `Nonempty (Turing.TM2Computable ea eb f)`. The second error is to forget the conditions of `Turing.haltList`: the machine must end with the initial store value and with all stacks other than the output stack empty. The third error is to read binary codes with the most significant bit first; Mathlib puts the least significant bit first. The fourth error is to look for a theorem that a `Partrec` function is `Turing.TM2Computable`; the index of this edition has no such declaration, and the result is `Turing.PartrecToTM2.tr_eval` with the code theorem.

### Exercises

1. (A) Compute $\mathrm{encodeNat}\ 13$ and $\mathrm{trList}[13, 0]$. Hint: $13 = 1 + 4 + 8$; the answers are $[\mathrm{true}, \mathrm{false}, \mathrm{true}, \mathrm{true}]$ and $[\mathrm{bit1}, \mathrm{bit0}, \mathrm{bit1}, \mathrm{bit1}, \mathrm{cons}, \mathrm{cons}]$.
2. (A) Show that the binary decoder maps both $[\mathrm{false}]$ and $[\mathrm{false}, \mathrm{true}]$ to $2$. Conclude that the decoder of an encoding need not be injective. Hint: the decoder maps $[]$ to $\mathrm{one}$ inside $\mathrm{PosNum}$.
3. (A) Prove that a function computable in polynomial time is Turing computable. Hint: compose the two forgetful maps.
4. (B) Prove that the decoder of the product encoding inverts its encoder. Hint: filtering the $\mathrm{inl}$ symbols out of the code of $(x, y)$ gives the code of $x$.
5. (B) Prove that $\mathbb{N} \to \mathrm{Bool}$ has no encoding over $\mathrm{Bool}$. Hint: use the countability bound and Cantor's diagonal argument.
6. (B) Trace the successor subroutine on $\mathrm{trList}[5]$ and on $\mathrm{trList}[0]$. Hint: $\mathrm{trList}[0] = [\mathrm{cons}]$, and the result must be $[\mathrm{bit1}, \mathrm{cons}]$.
7. (C) Show that the unary code of $n$ has length $n$ and the binary code has length $\lfloor \log_2 n \rfloor + 1$ for $n \ge 1$. Deduce that a time bound that is polynomial in the length of the unary code can be exponential in the length of the binary code. Hint: the length of the binary code is the number of bits of $n$.

### Notes and history

Turing showed in his 1936 paper that his machines compute the same functions as the lambda calculus of Church, and Kleene showed that these are the partial recursive functions. The Church-Turing thesis states that this class captures informal computability. Encodings with time bounds are the starting point of complexity theory, where the class of polynomial time functions does not change between encodings of polynomially related lengths, such as binary codes in different alphabets.

The Mathlib authors, from the file headers: `Mathlib.Computability.Encoding` and `Mathlib.Computability.TuringMachine.Computable` by Pim Spelier and Daan van Gent, and `Mathlib.Computability.TuringMachine.ToPartrec` by Mario Carneiro.

### Reference

<?reference?>
