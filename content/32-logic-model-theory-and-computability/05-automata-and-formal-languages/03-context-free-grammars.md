---
title: Context-free grammars
kind: theory
modules:
  - Mathlib.Computability.ContextFreeGrammar
explains:
  E3: [Symbol, ContextFreeRule, ContextFreeRule.Rewrites, ContextFreeRule.rewrites_iff, ContextFreeRule.Rewrites.append_left, ContextFreeGrammar, ContextFreeGrammar.Produces, ContextFreeGrammar.Derives, ContextFreeGrammar.Generates, ContextFreeGrammar.language, ContextFreeGrammar.mem_language_iff, ContextFreeGrammar.derives_nonterminal, Language.IsContextFree, ContextFreeGrammar.reverse, ContextFreeRule.rewrites_reverse, ContextFreeGrammar.language_reverse, Language.IsContextFree.reverse]
  E2: [ContextFreeRule.Rewrites.exists_parts, ContextFreeRule.rewrites_of_exists_parts, ContextFreeRule.Rewrites.input_output, ContextFreeRule.Rewrites.append_right, ContextFreeRule.Rewrites.nonterminal_input_mem, ContextFreeGrammar.Produces.single, ContextFreeGrammar.Derives.refl, ContextFreeGrammar.Derives.trans, ContextFreeGrammar.Derives.trans_produces, ContextFreeGrammar.Produces.trans_derives, ContextFreeGrammar.derives_iff_eq_or_head, ContextFreeGrammar.derives_iff_eq_or_tail, ContextFreeGrammar.Produces.append_left, ContextFreeGrammar.Derives.append_left, ContextFreeGrammar.Derives.append_right, ContextFreeGrammar.Produces.exists_nonterminal_input_mem, ContextFreeGrammar.language_eq_zero_of_forall_input_ne_initial, ContextFreeRule.reverse, ContextFreeGrammar.produces_reverse, ContextFreeGrammar.derives_reverse, ContextFreeGrammar.generates_reverse, ContextFreeGrammar.reverse_reverse, Language.IsContextFree.of_reverse, Language.isContextFree_reverse]
  E1: auto
families: []
requires: [V01.C01, V01.C02, V03.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Context-free grammars

### Overview

A grammar generates words instead of reading them. It starts from one symbol and rewrites symbols by rules until only letters remain. In a context-free grammar the left side of each rule is a single nonterminal symbol, so a rule can apply to that symbol wherever it stands. Context-free grammars describe the nested structure of brackets, of arithmetic expressions and of the syntax of programming languages, and they describe languages such as $\{a^n b^n\}$ that the previous section proved not regular.

Mathlib defines rules, single rewriting steps, derivations, and the language of a grammar. It proves that a rewriting step stays valid inside any context, and that the context-free languages are closed under reversal. This section proves these facts, and it computes the languages of two grammars by hand: the grammar $S \to aSb \mid \varepsilon$ and the grammar of balanced brackets.

### Definitions

**Definition (Symbol).** For a type $T$ of terminals (the letters) and a type $N$ of nonterminals, a symbol is either `Symbol.terminal t` with $t \in T$ or `Symbol.nonterminal A` with $A \in N$. A sentential form is a list of symbols. A word $w \in T^{*}$ gives the sentential form $\bar w$, the list of the terminals of $w$ (`w.map Symbol.terminal`).

**Definition (Rule).** A context-free rule is a pair $A \to \beta$ of a nonterminal $A$ (the field `input`) and a sentential form $\beta$ (the field `output`).

**Definition (Rewriting step).** A rule $A \to \beta$ rewrites $u$ to $v$ if $v$ comes from $u$ by the replacement of one occurrence of $A$ with $\beta$. Mathlib defines `ContextFreeRule.Rewrites` inductively. The constructor `head` rewrites $A :: s$ to $\beta \mathbin{+\!\!+} s$, and the constructor `cons` adds one symbol $x$ in front of both sides of a step.

**Definition (Grammar).** A context-free grammar over $T$ is a type `NT` of nonterminals, an initial nonterminal $S$ and a finite set of rules over $T$ and `NT`. The grammar produces $v$ from $u$ in one step, $u \Rightarrow v$, if some rule of the grammar rewrites $u$ to $v$. The grammar derives $v$ from $u$, $u \Rightarrow^{*} v$, if there is a finite chain $u = u_0 \Rightarrow u_1 \Rightarrow \cdots \Rightarrow u_k = v$ with $k \geq 0$. In Mathlib, `Derives` is the reflexive transitive closure `Relation.ReflTransGen` of `Produces`.

**Definition (Language of a grammar).** The grammar generates $u$ if $[S] \Rightarrow^{*} u$. Its language is $L(G) = \{w \in T^{*} : [S] \Rightarrow^{*} \bar w\}$. A language is context-free if it is the language of some context-free grammar (`Language.IsContextFree`).

The type `NT` lives in `Type` and can be infinite. Only finitely many nonterminals occur in the finitely many rules, so this freedom adds no languages.

**Definition (Reversed grammar).** The reverse of a rule $A \to \beta$ is $A \to \operatorname{rev}(\beta)$. The reverse of a grammar has the same nonterminals and initial symbol, and the reversed rules.

### Theorems and proofs

**Proposition (Shape of a step).** The rule $A \to \beta$ rewrites $u$ to $v$ if and only if there are sentential forms $p, q$ with $u = p \mathbin{+\!\!+} [A] \mathbin{+\!\!+} q$ and $v = p \mathbin{+\!\!+} \beta \mathbin{+\!\!+} q$.

*Proof.* From left to right, induction on the step. For `head s`, take $p = [\,]$ and $q = s$. For `cons x h`, the hypothesis of induction gives $p', q$ for the step $h$, and $p = x :: p'$ works. From right to left, induction on $p$. For $p = [\,]$ the step is `head q`. For $p = x :: p'$, apply `cons x` to the step for $p'$. $\square$

As a special case, $A \to \beta$ rewrites $[A]$ to $\beta$ (`Rewrites.input_output`), and a rewritten form contains $A$.

**Proposition (Context closure).** If $u \Rightarrow^{*} v$, then $p \mathbin{+\!\!+} u \Rightarrow^{*} p \mathbin{+\!\!+} v$ and $u \mathbin{+\!\!+} q \Rightarrow^{*} v \mathbin{+\!\!+} q$ for all $p, q$. The same holds for one step and for one rule.

*Proof.* For one rule, write $u = p' \mathbin{+\!\!+} [A] \mathbin{+\!\!+} q'$ and $v = p' \mathbin{+\!\!+} \beta \mathbin{+\!\!+} q'$ by the previous proposition. Then $p \mathbin{+\!\!+} u = (p \mathbin{+\!\!+} p') \mathbin{+\!\!+} [A] \mathbin{+\!\!+} q'$ and $p \mathbin{+\!\!+} v = (p \mathbin{+\!\!+} p') \mathbin{+\!\!+} \beta \mathbin{+\!\!+} q'$, which is a step by the converse direction. The right context is the same with $q' \mathbin{+\!\!+} q$. One step of the grammar is one step of a rule, and a derivation is a chain of steps, so induction on the length of the chain gives the claim for $\Rightarrow^{*}$. $\square$

Two derivations combine: if $u_1 \Rightarrow^{*} v_1$ and $u_2 \Rightarrow^{*} v_2$, then $u_1 \mathbin{+\!\!+} u_2 \Rightarrow^{*} v_1 \mathbin{+\!\!+} u_2 \Rightarrow^{*} v_1 \mathbin{+\!\!+} v_2$, by the right context and then the left context. The examples below use this fact.

**Lemma (First step).** $u \Rightarrow^{*} v$ holds if and only if $u = v$, or $u \Rightarrow w$ and $w \Rightarrow^{*} v$ for some $w$. The same holds with the last step in place of the first.

*Proof.* This is the description of a reflexive transitive closure by its first or by its last step: a chain of length $0$ gives $u = v$, and a chain of length $k + 1$ splits into one step and a chain of length $k$. $\square$

**Proposition (A nonterminal with no rule).** Let $A$ be a nonterminal that is the input of no rule. Then $[A]$ derives only itself. If $S$ is the input of no rule, then $L(G) = \varnothing$.

*Proof.* Suppose $[A] \Rightarrow^{*} s$ with $s \neq [A]$. By the lemma on the first step, $[A] \Rightarrow w$ for some $w$. Some rule $B \to \beta$ of the grammar makes this step, and then $B$ occurs in $[A]$, so $B = A$. This contradicts the hypothesis. For the second claim, a word $w$ in $L(G)$ gives $[S] \Rightarrow^{*} \bar w$, and $\bar w \neq [S]$ since $\bar w$ has no nonterminal. $\square$

**Theorem (Closure under reversal).** If $L$ is context-free, then $L^{R} = \{w : \operatorname{rev}(w) \in L\}$ is context-free. More precisely, $L(G^{R}) = L(G)^{R}$.

*Proof.* First, $A \to \operatorname{rev}(\beta)$ rewrites $\operatorname{rev}(u)$ to $\operatorname{rev}(v)$ if and only if $A \to \beta$ rewrites $u$ to $v$. Indeed, if $u = p \mathbin{+\!\!+} [A] \mathbin{+\!\!+} q$ and $v = p \mathbin{+\!\!+} \beta \mathbin{+\!\!+} q$, then $$\operatorname{rev}(u) = \operatorname{rev}(q) \mathbin{+\!\!+} [A] \mathbin{+\!\!+} \operatorname{rev}(p), \qquad \operatorname{rev}(v) = \operatorname{rev}(q) \mathbin{+\!\!+} \operatorname{rev}(\beta) \mathbin{+\!\!+} \operatorname{rev}(p),$$ which is a step of the reversed rule by the shape of a step. The converse is the same argument applied to the reversed rule, since the reverse of the reverse is the rule itself. The rules of $G^{R}$ are the reverses of the rules of $G$, so $\operatorname{rev}(u) \Rightarrow_{G^R} \operatorname{rev}(v)$ if and only if $u \Rightarrow_G v$. Induction on the length of a chain gives the same for $\Rightarrow^{*}$. The form $[S]$ is its own reverse, and $\operatorname{rev}(\bar w) = \overline{\operatorname{rev}(w)}$. So $$w \in L(G^R) \iff [S] \Rightarrow^{*}_{G^{R}} \bar w \iff [S] \Rightarrow^{*}_{G} \overline{\operatorname{rev}(w)} \iff \operatorname{rev}(w) \in L(G). \qquad \square$$

Since reversal is an involution, $L$ is context-free if and only if $L^{R}$ is (`Language.isContextFree_reverse`).

**Remark (What the index has).** Reversal is the only closure property of this file. The index of this edition has no declaration for the closure of context-free languages under union, concatenation or star, for the fact that each regular language is context-free, for the pumping lemma for context-free languages, or for the equivalence of grammars with pushdown automata. The constructions are standard. For union, add a new initial symbol $S_0$ with the rules $S_0 \to S_1$ and $S_0 \to S_2$, over the disjoint union of the two types of nonterminals. For a DFA with states $Q$, take the nonterminals $Q$, initial symbol $s_0$, a rule $q \to a\,\delta(q, a)$ for each $q$ and $a$, and a rule $q \to \varepsilon$ for each $q \in F$.

### Examples

**Example (The language $a^n b^n$).** Let $T = \{a, b\}$, let `NT` have one element $S$, and let the rules be $S \to aSb$ and $S \to \varepsilon$. Then $L(G) = \{a^n b^n : n \geq 0\}$.

*Proof.* First, each sentential form that $[S]$ derives is $a^n S b^n$ or $a^n b^n$ for some $n$. Use induction on the derivation, with the lemma on the last step. The form $[S]$ is $a^0 S b^0$. Suppose $[S] \Rightarrow^{*} u \Rightarrow v$ and $u$ has one of the two shapes. The form $a^n b^n$ has no nonterminal, so no step starts from it. So $u = a^n S b^n$, and its only nonterminal is the middle $S$. By the shape of a step, $p = a^n$ and $q = b^n$, and $v$ is $a^{n+1} S b^{n+1}$ or $a^n b^n$. Second, $[S] \Rightarrow^{*} a^n S b^n$ by induction on $n$: apply $S \to aSb$ in the context $a^n$ and $b^n$. One more step with $S \to \varepsilon$ gives $a^n b^n$. So the terminal forms that $[S]$ derives are exactly the words $a^n b^n$. $\square$

So $\{a^n b^n\}$ is context-free and, by the previous section, not regular. The derivation of $aabb$ is $S \Rightarrow aSb \Rightarrow aaSbb \Rightarrow aabb$.

**Example (Balanced brackets).** Let $T = \{(, )\}$, let `NT` have one element $S$, and let the rules be $S \to \varepsilon$ and $S \to (S)S$. Call a word balanced if it has as many letters $($ as letters $)$, and each prefix has at least as many $($ as $)$. Then $L(G)$ is the set of balanced words.

*Proof.* For a sentential form $u$, let $u^{\circ}$ be the word that remains after the deletion of each $S$. First, $u^{\circ}$ is balanced whenever $[S] \Rightarrow^{*} u$. For $[S]$ the deleted form is the empty word. A step with $S \to \varepsilon$ does not change $u^{\circ}$. A step with $S \to (S)S$ inserts the word $()$ into $u^{\circ}$ at one position. Let the height of a prefix be the number of $($ minus the number of $)$. Before the insertion point the heights do not change, at the inserted letters they are $h + 1$ and $h$ with $h \geq 0$, and after it they do not change. So the new word is balanced. For a word $w$, $\bar w^{\circ} = w$, so each word of $L(G)$ is balanced.

Second, $[S] \Rightarrow^{*} \bar w$ for each balanced $w$, by strong induction on $|w|$. For $w$ empty, use $S \to \varepsilon$. Otherwise the first letter is $($, since the prefix of length $1$ has height at least $0$. Let $2k$ be the least positive length of a prefix of height $0$; it exists since $w$ has height $0$. Then $w = (\, u \,)\, v$ with $|u| = 2k - 2$. The word $u$ is balanced, since its prefix heights are those of $w$ minus one, and the heights of $w$ stay positive strictly between $0$ and $2k$. The word $v$ is balanced, since its prefix heights are those of $w$ after position $2k$. Both are shorter than $w$. So $$[S] \Rightarrow (S)S \Rightarrow^{*} (\bar u)S \Rightarrow^{*} (\bar u)\bar v,$$ by the hypothesis of induction and the context closure. $\square$

A derivation of $(())()$, with the leftmost $S$ rewritten each time: $$S \Rightarrow (S)S \Rightarrow ((S)S)S \Rightarrow (()S)S \Rightarrow (())S \Rightarrow (())(S)S \Rightarrow (())()S \Rightarrow (())().$$ It has seven steps: two applications of $S \to (S)S$ and five of $S \to \varepsilon$.

**Example (Reversal of $a^n b^n$).** The reversed grammar of the first example has the rules $S \to bSa$ and $S \to \varepsilon$. By the theorem on reversal its language is $\{b^n a^n : n \geq 0\}$, which is the reverse of $\{a^n b^n\}$.

**Counterexample (A rule that never fires).** Let `NT` be $\{S, A\}$ with initial symbol $S$, and let the only rule be $A \to a$. No rule has input $S$, so $L(G) = \varnothing$ by the proposition on nonterminals with no rule, although the rule $A \to a$ produces a word from $A$.

### The library around it

::: mathlib
`ContextFreeRule.Rewrites` · `Mathlib.Computability.ContextFreeGrammar`

`Symbol T N` has the constructors `terminal` and `nonterminal`, and `ContextFreeRule T N` has the fields `input` and `output`. `ContextFreeRule.Rewrites r u v` is the inductive step with the constructors `head` and `cons`. `rewrites_iff` gives the description by parts, from `Rewrites.exists_parts` and `rewrites_of_exists_parts`. `Rewrites.input_output`, `Rewrites.nonterminal_input_mem`, `Rewrites.append_left` and `Rewrites.append_right` are the basic facts.

<?decl ContextFreeRule.Rewrites?>
:::

::: mathlib
`ContextFreeGrammar` · `Mathlib.Computability.ContextFreeGrammar`

`ContextFreeGrammar T` has the fields `NT : Type`, `initial : NT` and `rules : Finset (ContextFreeRule T NT)`. `Produces` is one step by a rule in `rules`, and `Derives` is `Relation.ReflTransGen g.Produces`, with `Derives.refl`, `Produces.single`, `Derives.trans`, `Derives.trans_produces` and `Produces.trans_derives`. `derives_iff_eq_or_head` and `derives_iff_eq_or_tail` split off the first or the last step. `Produces.append_left`, `Derives.append_left` and `Derives.append_right` are the context closure.

<?decl ContextFreeGrammar?>
:::

::: mathlib
`ContextFreeGrammar.language` · `Mathlib.Computability.ContextFreeGrammar`

`g.Generates s` is `g.Derives [Symbol.nonterminal g.initial] s`, and `g.language` is `{w | g.Generates (w.map Symbol.terminal)}`, with `mem_language_iff`. `derives_nonterminal` and `language_eq_zero_of_forall_input_ne_initial` treat a nonterminal with no rule.

<?decl ContextFreeGrammar.language?>
:::

::: mathlib
`Language.IsContextFree.reverse` · `Mathlib.Computability.ContextFreeGrammar`

`Language.IsContextFree L` is `∃ g : ContextFreeGrammar T, g.language = L`. `ContextFreeRule.reverse` and `ContextFreeGrammar.reverse` reverse the outputs, with `rewrites_reverse`, `produces_reverse`, `derives_reverse`, `generates_reverse` and `language_reverse : g.reverse.language = g.language.reverse`. `IsContextFree.reverse`, `IsContextFree.of_reverse` and `isContextFree_reverse` are the closure statements.

<?decl Language.IsContextFree.reverse?>
:::

::: mathlib
`Relation.ReflTransGen` · `Mathlib.Logic.Relation`

The reflexive transitive closure of a relation, with the constructors `refl` and `tail`. Its induction principles `head_induction_on` and the induction on `tail` give the proofs by induction on the length of a derivation.

<?decl Relation.ReflTransGen?>
:::

Common errors of a learner: The first error is to write a word of the language where Lean expects a sentential form; `g.language` contains `w : List T`, and the derivation ends at `w.map Symbol.terminal`. The second error is to build `rules` as a list; the field is a `Finset`, and a literal such as `{r₁, r₂}` needs the derived `DecidableEq` instance on rules, which exists. The third error is to prove a property of all derived forms by induction on `Derives` without the right motive; generalize the final form and use `Relation.ReflTransGen.head_induction_on` or the induction on `tail`. The fourth error is to look for closure under union in this file; the index of this edition has no declaration for it.

### Exercises

1. (A) Give a derivation of $aaabbb$ in the grammar $S \to aSb \mid \varepsilon$, and write each step as $p \mathbin{+\!\!+} [S] \mathbin{+\!\!+} q \Rightarrow p \mathbin{+\!\!+} \beta \mathbin{+\!\!+} q$. Hint: $p = a^n$ and $q = b^n$ at step $n$.
2. (A) Give a grammar for the palindromes over $\{a, b\}$, and derive $abba$ and $aba$. Hint: $S \to aSa \mid bSb \mid a \mid b \mid \varepsilon$.
3. (A) Show that $L(G) = \{[\,]\}$ for the grammar with the single rule $S \to \varepsilon$, and that $L(G) = \varnothing$ for the grammar with the single rule $S \to S$. Hint: for the second, each derived form is $[S]$.
4. (B) Give a grammar for $\{a^i b^j : i \leq j\}$, and prove that its language is this set. Hint: $S \to aSb \mid Sb \mid \varepsilon$; the derived forms are $a^i S b^j$ and $a^i b^j$ with $i \leq j$.
5. (B) Give a grammar for the words over $\{a, b\}$ with as many $a$ as $b$. Prove that each word of the language has this property. Hint: $S \to aSbS \mid bSaS \mid \varepsilon$, and each rule keeps the difference of the counts.
6. (B) Prove that the grammar with the rules $S \to SS$, $S \to (S)$ and $S \to \varepsilon$ also generates the set of balanced words. Hint: the deletion argument gives one inclusion; for the other, simulate the rule $S \to (S)S$ by $S \Rightarrow SS \Rightarrow (S)S$.
7. (C) Complete the remark on regular languages: for a DFA $M$ with a finite set of states, prove that the grammar with the rules $q \to a\,\delta(q, a)$ and $q \to \varepsilon$ for $q \in F$ generates $L(M)$. Hint: prove that $[q] \Rightarrow^{*} \bar x\, [q']$ if and only if $\delta^{*}(q, x) = q'$, by induction on $x$.

### Notes and history

Chomsky introduced the hierarchy of grammars, with context-free grammars as one level, in the 1950s. Backus and Naur used the same formalism to describe the syntax of ALGOL 60. The pumping lemma for context-free languages is due to Bar-Hillel, Perles and Shamir.

The Mathlib file `Mathlib.Computability.ContextFreeGrammar` is by Martin Dvorak, read from its header.

### Reference

<?reference?>
