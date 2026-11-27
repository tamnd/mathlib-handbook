---
title: Finite automata and the Myhill-Nerode theorem
kind: theory
modules:
  - Mathlib.Computability.DFA
  - Mathlib.Computability.NFA
  - Mathlib.Computability.EpsilonNFA
  - Mathlib.Computability.MyhillNerode
explains:
  E3: [DFA, DFA.evalFrom, DFA.evalFrom_of_append, DFA.accepts, Language.IsRegular, DFA.union, DFA.accepts_union, DFA.pumping_lemma, NFA, NFA.stepSet, NFA.toDFA, NFA.toDFA_correct, εNFA, εNFA.εClosure, εNFA.toNFA_correct, NFA.reverse, NFA.mem_accepts_reverse, Language.leftQuotient, Language.leftQuotient_append, Language.leftQuotient_accepts_apply, Language.toDFA, Language.accepts_toDFA, Language.isRegular_iff_finite_range_leftQuotient]
  E2: [DFA.eval, DFA.acceptsFrom, DFA.mem_accepts, DFA.eval_append_singleton, DFA.evalFrom_split, DFA.inter, DFA.accepts_inter, DFA.accepts_compl, DFA.comap, DFA.reindex, Language.isRegular_iff, Language.IsRegular.compl, Language.IsRegular.add, Language.IsRegular.inf, Language.IsRegular.reverse, Language.isRegular_reverse_iff, NFA.evalFrom, NFA.accepts, NFA.Path, NFA.accepts_iff_exists_path, NFA.pumping_lemma, DFA.toNFA, DFA.toNFA_correct, εNFA.toNFA, εNFA.εClosure_min, εNFA.IsPath, εNFA.mem_accepts_iff_exists_path, NFA.toεNFA, NFA.toεNFA_correct, Language.mem_leftQuotient, Language.IsRegular.finite_range_leftQuotient, Language.IsRegular.of_finite_range_leftQuotient]
  E1: auto
families: []
requires: [V01.C02, V03.C02, V03.C04, V03.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Finite automata and the Myhill-Nerode theorem

### Overview

A finite automaton reads a word one letter at a time and keeps only a bounded amount of memory, its current state. The languages that such a machine recognizes are the regular languages. This section defines deterministic automata (DFA), nondeterministic automata (NFA) and automata with silent moves ($\varepsilon$-NFA), and proves that the three models recognize the same languages. It then proves the two standard tools to show that a language is not regular: the pumping lemma and the Myhill-Nerode theorem. The running examples are a DFA for the binary numerals of multiples of $3$, and the language $\{a^n b^n : n \geq 0\}$, which is not regular.

Mathlib allows automata with any type of states. Finiteness enters only in the definition of a regular language, through a `Fintype` instance on the states.

### Definitions

**Definition (DFA).** A deterministic automaton over the alphabet $\alpha$ with states $\sigma$ is a triple $M = (\delta, s_0, F)$ of a transition function $\delta \colon \sigma \to \alpha \to \sigma$ (the field `step`), a start state $s_0$ (`start`) and a set $F \subseteq \sigma$ of accepting states (`accept`). The run from a state $s$ on a word is the left fold $$\delta^{*}(s, [\,]) = s, \qquad \delta^{*}(s, a :: x) = \delta^{*}(\delta(s, a), x),$$ which is `M.evalFrom s x`, and `M.eval x` is $\delta^{*}(s_0, x)$. The language of $M$ from $s$ is $\{x : \delta^{*}(s, x) \in F\}$ (`acceptsFrom s`), and the language of $M$ is the case $s = s_0$ (`accepts`).

**Definition (Regular language).** A language $L$ over $\alpha$ is regular if there are a finite type $\sigma$ and a DFA $M$ with states $\sigma$ and $L(M) = L$. In Mathlib, `L.IsRegular` asks for `σ : Type`, a `Fintype σ` instance and `M : DFA α σ` with `M.accepts = L`.

**Definition (NFA).** A nondeterministic automaton has a transition function $\delta \colon \sigma \to \alpha \to \mathcal{P}(\sigma)$, a set of start states $I$ and a set of accepting states $F$. For a set $S$ of states, $\delta(S, a) = \bigcup_{s \in S} \delta(s, a)$ (`stepSet`), and the run on a word is again the left fold, now on sets of states. A word $x$ is accepted if the run from $I$ on $x$ meets $F$. A path from $s$ to $t$ on $x$ (the type `NFA.Path`) is a sequence of states in which each step follows a transition labelled by the next letter of $x$.

**Definition ($\varepsilon$-NFA).** An $\varepsilon$-NFA has a transition function $\delta \colon \sigma \to \text{Option}\ \alpha \to \mathcal{P}(\sigma)$. A transition on `none` is a silent move, which reads no letter. The $\varepsilon$-closure of a set $S$ is the set of states reachable from $S$ by finitely many silent moves; it is the least superset of $S$ closed under silent moves. The run first closes the start set, and after each letter it closes again: $\delta(S, a) = \bigcup_{s \in S} \operatorname{cl}(\delta(s, a))$.

**Definition (Left quotient).** For a language $L$ and a word $x$, the left quotient is $x^{-1} L = \{y : x \mathbin{+\!\!+} y \in L\}$ (`L.leftQuotient x`).

The left quotient $x^{-1}L$ is what remains to be read after $x$: it is all that a recognizer of $L$ must remember about $x$.

### Theorems and proofs

**Proposition (Runs on a concatenation).** For a DFA, $\delta^{*}(s, x \mathbin{+\!\!+} y) = \delta^{*}(\delta^{*}(s, x), y)$. In particular $\delta^{*}(s, x \mathbin{+\!\!+} [a]) = \delta(\delta^{*}(s, x), a)$.

*Proof.* Induction on $x$, for all $s$. For $x = [\,]$ both sides are $\delta^{*}(s, y)$. For $a :: x$, both sides are $\delta^{*}(\delta^{*}(\delta(s, a), x), y)$ by the definition and the hypothesis of induction at $\delta(s, a)$. $\square$

**Theorem (Boolean closure).** If $L_1$ and $L_2$ are regular, then $L_1^{c}$, $L_1 \cup L_2$ and $L_1 \cap L_2$ are regular.

*Proof.* Let $M = (\delta, s_0, F)$ recognize $L_1$. The DFA $(\delta, s_0, \sigma \setminus F)$ has the same runs, and accepts $x$ exactly when $M$ rejects $x$. For the union, let $M_i = (\delta_i, s_i, F_i)$ have states $\sigma_i$. The product automaton has states $\sigma_1 \times \sigma_2$, transition $\delta((p, q), a) = (\delta_1(p, a), \delta_2(q, a))$ and start $(s_1, s_2)$. By induction on $x$, its run from $(p, q)$ on $x$ is $(\delta_1^{*}(p, x), \delta_2^{*}(q, x))$. With the accepting set $\{(p, q) : p \in F_1 \text{ or } q \in F_2\}$ it recognizes $L_1 \cup L_2$, and with "and" in place of "or" it recognizes $L_1 \cap L_2$. A product of two finite types is finite. $\square$

**Theorem (Subset construction).** Let $N$ be an NFA with states $\sigma$. The DFA $N^{\mathrm{det}}$ with states $\mathcal{P}(\sigma)$, transition $S \mapsto \delta(S, a)$, start $I$ and accepting sets $\{S : S \cap F \neq \varnothing\}$ recognizes the same language. Conversely, a DFA $(\delta, s_0, F)$ is the NFA with transitions $\{\delta(s, a)\}$ and start $\{s_0\}$. So a language is regular if and only if a finite NFA recognizes it.

*Proof.* The run of $N^{\mathrm{det}}$ on $x$ is the left fold of $S \mapsto \delta(S, a)$ from $I$, and this is by definition the run of $N$ on $x$. So $N^{\mathrm{det}}$ accepts $x$ if and only if the run of $N$ meets $F$. For the converse, induction on $x$ shows that the set run of the NFA from $\{s\}$ is the singleton $\{\delta^{*}(s, x)\}$. If $\sigma$ is finite, so is $\mathcal{P}(\sigma)$. $\square$

**Theorem (Silent moves).** Let $E$ be an $\varepsilon$-NFA. The NFA with transitions $s \mapsto \operatorname{cl}(\delta(s, a))$, start $\operatorname{cl}(I)$ and the same accepting states recognizes the language of $E$. Conversely, an NFA is the $\varepsilon$-NFA with no silent moves.

*Proof.* The set run of $E$ is the fold of $S \mapsto \bigcup_{s \in S} \operatorname{cl}(\delta(s, a))$ from $\operatorname{cl}(I)$. This is the transition of the new NFA, from its start set, so the two runs agree word by word. With no silent moves, the closure of a set is the set itself. $\square$

In Mathlib, `εNFA.toNFA_correct` holds by `rfl`: the definitions are made to agree.

**Theorem (Reversal).** If $L$ is regular, so is $L^{R} = \{x : \operatorname{rev}(x) \in L\}$.

*Proof.* Let $N = (\delta, I, F)$ be an NFA for $L$. The reversed NFA has the transition $\delta^{R}(t, a) = \{s : t \in \delta(s, a)\}$, start $F$ and accepting set $I$. A path $s_0 \xrightarrow{a_1} s_1 \cdots \xrightarrow{a_k} s_k$ of $N$ is the same as a path $s_k \xrightarrow{a_k} \cdots \xrightarrow{a_1} s_0$ of $N^R$, so $N^{R}$ accepts $x$ if and only if $N$ accepts $\operatorname{rev}(x)$. Apply the subset construction to $N^R$, with the NFA of a DFA for $L$. $\square$

Mathlib proves the statement on paths as a statement on disjointness: the set run of $N^{R}$ from $S'$ on $x$ misses $S$ if and only if the run of $N$ from $S$ on $\operatorname{rev}(x)$ misses $S'$, by induction on $x$.

**Theorem (Pumping lemma).** Let $M$ be a DFA with a finite set of $k$ states, and let $x \in L(M)$ with $|x| \geq k$. Then $x = u v w$ with $|u| + |v| \leq k$, $v \neq [\,]$, and $u v^{i} w \in L(M)$ for all $i \geq 0$.

*Proof.* Consider the $k + 1$ states $q_j = \delta^{*}(s_0, x_{<j})$ for $j = 0, \dots, k$, where $x_{<j}$ is the prefix of length $j$. By the pigeonhole principle, $q_m = q_n$ for some $m < n \leq k$. Let $u = x_{<m}$, let $v$ be the letters of $x$ at positions $m, \dots, n - 1$, and let $w$ be the rest. Then $|u| + |v| = n \leq k$ and $v \neq [\,]$. Put $q = q_m$. By the proposition on concatenations, $\delta^{*}(q, v) = q_n = q$, and by induction on $i$, $\delta^{*}(q, v^i) = q$. So $$\delta^{*}(s_0, u v^i w) = \delta^{*}(\delta^{*}(q, v^i), w) = \delta^{*}(q, w) = \delta^{*}(s_0, x) \in F. \qquad \square$$

Mathlib states the conclusion as `{u} * {v}∗ * {w} ≤ M.accepts`, which covers all $i$ at once. The NFA version applies the DFA version to the subset construction, so its bound is $2^k$ for an NFA with $k$ states.

**Lemma (Quotients and runs).** For each $x, y$: $(x \mathbin{+\!\!+} y)^{-1} L = y^{-1}(x^{-1} L)$. For a DFA $M$, $x^{-1} L(M)$ is the language of $M$ from the state $\delta^{*}(s_0, x)$.

*Proof.* The word $z$ is in $(x \mathbin{+\!\!+} y)^{-1}L$ if and only if $x \mathbin{+\!\!+} y \mathbin{+\!\!+} z \in L$, if and only if $y \mathbin{+\!\!+} z \in x^{-1}L$. For the second claim, $y \in x^{-1}L(M)$ if and only if $\delta^{*}(s_0, x \mathbin{+\!\!+} y) \in F$, and $\delta^{*}(s_0, x \mathbin{+\!\!+} y) = \delta^{*}(\delta^{*}(s_0, x), y)$. $\square$

**Theorem (Myhill-Nerode).** A language $L$ is regular if and only if the set $\{x^{-1}L : x \in \alpha^{*}\}$ of its left quotients is finite.

*Proof.* Suppose $M$ is a DFA for $L$ with a finite set of states. By the lemma, $x^{-1}L$ is the language of $M$ from $\delta^{*}(s_0, x)$, so the map $x \mapsto x^{-1}L$ factors through the finite set of states. Its range is finite.

Conversely, suppose the set $Q$ of left quotients is finite. Define a DFA with states $Q$, start $L = [\,]^{-1}L$, transition $\delta(K, a) = [a]^{-1}K$ and accepting set $\{K : [\,] \in K\}$. The transition stays in $Q$: if $K = x^{-1}L$, then $[a]^{-1}K = (x \mathbin{+\!\!+} [a])^{-1}L$ by the lemma. Prove $\delta^{*}(L, x) = x^{-1}L$ by induction on $x$ from the right. For $x = [\,]$ it is the start. For $x \mathbin{+\!\!+} [a]$, $$\delta^{*}(L, x \mathbin{+\!\!+} [a]) = [a]^{-1}(\delta^{*}(L, x)) = [a]^{-1}(x^{-1}L) = (x \mathbin{+\!\!+} [a])^{-1}L.$$ So the automaton accepts $x$ if and only if $[\,] \in x^{-1}L$, that is, $x \in L$. $\square$

The automaton of the proof is the minimal DFA of $L$: by the first half, each DFA for $L$ has at least as many reachable states as $L$ has left quotients. The index of this edition has no declaration for this minimality.

### Examples

**Example (Multiples of three in binary).** Let $\alpha = \{0, 1\}$ and read a word $b_1 \cdots b_k$ as the binary numeral $\nu(b_1 \cdots b_k) = \sum_j b_j 2^{k - j}$, most significant bit first. Let $\sigma = \{0, 1, 2\}$, $s_0 = 0$, $F = \{0\}$ and $\delta(q, b) = (2q + b) \bmod 3$. Then $\delta^{*}(0, x) = \nu(x) \bmod 3$ for each $x$. The proof is an induction from the right: $\nu([\,]) = 0$, and $\nu(x \mathbin{+\!\!+} [b]) = 2\nu(x) + b$, so $$\delta^{*}(0, x \mathbin{+\!\!+} [b]) = (2(\nu(x) \bmod 3) + b) \bmod 3 = (2\nu(x) + b) \bmod 3.$$ So $M$ accepts exactly the numerals of multiples of $3$, the empty word included (its value is $0$). On $110$ (six) the run is $0 \xrightarrow{1} 1 \xrightarrow{1} 0 \xrightarrow{0} 0$, accepted. On $1001$ (nine) it is $0 \xrightarrow{1} 1 \xrightarrow{0} 2 \xrightarrow{0} 1 \xrightarrow{1} 0$, accepted. On $111$ (seven) it is $0 \to 1 \to 0 \to 1$, rejected. The three left quotients of the language are the sets $\{y : \nu(x \mathbin{+\!\!+} y) \equiv 0\}$ for $\nu(x) \equiv 0, 1, 2$, and they are distinct ($[\,]$, $[1]$ and $[0, 1]$ separate them), so this DFA is minimal.

**Example (Subset construction).** Let $L$ be the set of binary words whose second letter from the end is $1$. An NFA with states $\{0, 1, 2\}$ guesses the position: $0$ loops on both letters, $0 \xrightarrow{1} 1$, $1 \xrightarrow{0, 1} 2$, start $\{0\}$, accepting $\{2\}$. The subset construction from $\{0\}$ reaches four sets: $$\{0\} \xrightarrow{0} \{0\},\ \{0\} \xrightarrow{1} \{0,1\},\ \{0,1\} \xrightarrow{0} \{0,2\},\ \{0,1\} \xrightarrow{1} \{0,1,2\},$$ $$\{0,2\} \xrightarrow{0} \{0\},\ \{0,2\} \xrightarrow{1} \{0,1\},\ \{0,1,2\} \xrightarrow{0} \{0,2\},\ \{0,1,2\} \xrightarrow{1} \{0,1,2\}.$$ The accepting sets are those that contain $2$: $\{0, 2\}$ and $\{0, 1, 2\}$. The four reachable sets record the last two letters, and the other four subsets are never reached.

**Counterexample (The language $a^n b^n$).** Let $L = \{a^n b^n : n \geq 0\}$ over $\{a, b\}$. For $i \neq j$, the word $b^i$ is in $(a^i)^{-1}L$ and not in $(a^j)^{-1}L$. So the left quotients $(a^i)^{-1}L$ are pairwise distinct, there are infinitely many, and $L$ is not regular by the Myhill-Nerode theorem. The pumping lemma gives a second proof. If a DFA with $k$ states recognized $L$, take $x = a^k b^k$. Then $x = uvw$ with $|uv| \leq k$, so $v = a^m$ with $m \geq 1$, and $uw = a^{k - m} b^k \notin L$, a contradiction.

**Remark (Infinite automata).** A `DFA α σ` with infinite $\sigma$ can recognize any language. The automaton of the proof of Myhill-Nerode, on the type of all left quotients, recognizes $L$ with no finiteness assumption (`Language.accepts_toDFA` has none). This is why `IsRegular` asks for `Fintype σ`.

### The library around it

::: mathlib
`DFA` · `Mathlib.Computability.DFA`

`DFA α σ` is a structure with the fields `step`, `start` and `accept`. `evalFrom s` is `List.foldl M.step s`, with the simp lemmas `evalFrom_nil`, `evalFrom_cons` and `eval_append_singleton`, and `evalFrom_of_append` for a concatenation. `acceptsFrom`, `accepts` and `mem_accepts : x ∈ M.accepts ↔ M.eval x ∈ M.accept` give the languages. The complement is an instance with `accepts_compl`, and `union` and `inter` build the product automata with `accepts_union` and `accepts_inter`. `comap f` changes the alphabet along `f`, and `reindex g` transports a DFA along an equivalence of states.

<?decl DFA?>
:::

::: mathlib
`Language.IsRegular` · `Mathlib.Computability.DFA`

`L.IsRegular` is `∃ σ : Type, ∃ _ : Fintype σ, ∃ M : DFA T σ, M.accepts = L`. `isRegular_iff` allows a state type in any universe. The closure lemmas are `IsRegular.compl`, `IsRegular.add` (union), `IsRegular.inf` (intersection) and, in the NFA file, `IsRegular.reverse` and `isRegular_reverse_iff`. The index of this edition has no declaration for the closure of regular languages under concatenation or under the star.

<?decl Language.IsRegular?>
:::

::: mathlib
`DFA.pumping_lemma` · `Mathlib.Computability.DFA`

`pumping_lemma [Fintype σ] (hx : x ∈ M.accepts) (hlen : Fintype.card σ ≤ x.length)` gives `a b c` with `x = a ++ b ++ c`, `a.length + b.length ≤ Fintype.card σ`, `b ≠ []` and `{a} * {b}∗ * {c} ≤ M.accepts`. The core is `evalFrom_split`, which finds the loop by the pigeonhole principle. `NFA.pumping_lemma` and `εNFA.pumping_lemma` have the bound `Fintype.card (Set σ)`.

<?decl DFA.pumping_lemma?>
:::

::: mathlib
`NFA.toDFA` · `Mathlib.Computability.NFA`

`NFA α σ` has `step : σ → α → Set σ`, `start : Set σ` and `accept : Set σ`. `stepSet`, `evalFrom`, `eval` and `accepts` are as in the text, and `accepts_iff_exists_path` describes acceptance by an `NFA.Path`. `toDFA : DFA α (Set σ)` is the subset construction, and `toDFA_correct : M.toDFA.accepts = M.accepts`. `DFA.toNFA` and `DFA.toNFA_correct` go back. `NFA.reverse` is the reversed automaton, with `mem_accepts_reverse : x ∈ M.reverse.accepts ↔ x.reverse ∈ M.accepts`.

<?decl NFA.toDFA?>
:::

::: mathlib
`εNFA` · `Mathlib.Computability.EpsilonNFA`

`εNFA α σ` has `step : σ → Option α → Set σ`. `εClosure S` is defined by a private inductive predicate, and the interface is `subset_εClosure`, `mem_εClosure_of_mem_step`, `εClosure_induction` and `εClosure_min`, which says that the closure is the least closed superset. `IsPath` is a path with silent letters, and `mem_accepts_iff_exists_path` reads acceptance from it. `toNFA` and `toNFA_correct` remove the silent moves, and `NFA.toεNFA` with `NFA.toεNFA_correct` adds none.

<?decl εNFA?>
:::

::: mathlib
`Language.isRegular_iff_finite_range_leftQuotient` · `Mathlib.Computability.MyhillNerode`

The Myhill-Nerode theorem: `L.IsRegular ↔ (Set.range L.leftQuotient).Finite`. The parts are `leftQuotient_append`, `leftQuotient_accepts_apply : leftQuotient M.accepts x = M.acceptsFrom (M.eval x)`, `IsRegular.finite_range_leftQuotient`, the automaton `L.toDFA : DFA α (Set.range L.leftQuotient)` with `accepts_toDFA`, and `IsRegular.of_finite_range_leftQuotient`.

<?decl Language.isRegular_iff_finite_range_leftQuotient?>
:::

Common errors of a learner: The first error is to prove a statement about `M.accepts` and forget that `DFA α σ` does not assume `σ` finite; the pumping lemma needs `[Fintype σ]`. The second error is to look for a lemma on `eval` and find it only for `evalFrom`; Mathlib keeps two simp sets, and `simp [DFA.eval]` passes from one to the other. The third error is to expect the NFA pumping lemma with the bound `Fintype.card σ`; the bound in the library is `Fintype.card (Set σ)`. The fourth error is to state `IsRegular` with a state type in a higher universe; use `Language.isRegular_iff` to change the universe.

### Exercises

1. (A) Run the DFA for multiples of three on $10010$ and on $1111$, and check the answers against the values $18$ and $15$. Hint: both are multiples of $3$.
2. (A) Build a DFA with four states for the binary words with an even number of $0$ and an even number of $1$, as a product of two automata. Hint: each factor has two states.
3. (A) Show that the language of all words over $\alpha$ has one left quotient, and that $\{[\,]\}$ has two. Hint: compute $x^{-1}L$ for $x = [\,]$ and for $x \neq [\,]$.
4. (B) Use the Myhill-Nerode theorem to show that the set of binary palindromes is not regular. Hint: the words $10^i$ have distinct left quotients; separate them with $0^i 1$.
5. (B) Generalize the first example: for $m \geq 1$, give a DFA with $m$ states for the binary numerals of multiples of $m$, and prove that it is correct. Hint: $\delta(q, b) = (2q + b) \bmod m$ and the same induction.
6. (B) Prove that the language $\{a^{n^2} : n \geq 0\}$ over one letter is not regular with the pumping lemma. Hint: with $k$ states, pump $a^{k^2}$ once; the length $k^2 + m$ with $1 \leq m \leq k$ lies strictly between $k^2$ and $(k+1)^2$.
7. (C) Show that the language of words whose $n$-th letter from the end is $1$ needs at least $2^n$ states in a DFA, while an NFA with $n + 1$ states recognizes it. Hint: the $2^n$ words of length $n$ have pairwise distinct left quotients.

### Notes and history

Finite automata in the form used here come from the work of Rabin and Scott, who introduced nondeterministic automata and the subset construction in 1959. Kleene's theorem of 1956 relates them to regular expressions. Myhill and Nerode proved the characterization by left quotients in 1957 and 1958, in the form of right congruences of finite index. The pumping lemma for regular languages is usually credited to Bar-Hillel, Perles and Shamir.

The Mathlib files are by these authors, read from their headers: `Mathlib.Computability.DFA` by Fox Thomson, Chris Wong and Rudy Peterson, `Mathlib.Computability.NFA` by Fox Thomson, Maja Kądziołka, Chris Wong and Rudy Peterson, `Mathlib.Computability.EpsilonNFA` by Fox Thomson, Yaël Dillies and Anthony DeRossi, and `Mathlib.Computability.MyhillNerode` by Chris Wong.

### Reference

<?reference?>
