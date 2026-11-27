---
title: Languages and regular expressions
kind: theory
modules:
  - Mathlib.Computability.Language
  - Mathlib.Computability.RegularExpressions
explains:
  E3: [Language, Language.mem_mul, Language.mem_kstar, Language.mem_kstar_iff_exists_nonempty, Language.mem_pow, Language.kstar_eq_iSup_pow, Language.one_add_self_mul_kstar_eq_kstar, Language.self_eq_mul_add_iff, Language.reverse_mul, RegularExpression, RegularExpression.matches', RegularExpression.matchEpsilon, RegularExpression.deriv, RegularExpression.rmatch, RegularExpression.rmatch_iff_matches']
  E2: [Language.mem_add, Language.mem_one, Language.nil_mem_kstar, Language.add_self, Language.le_iff, Language.mem_inf, Language.instSemiring, Language.instKleeneAlgebra, Language.mul_self_kstar_comm, Language.one_add_kstar_mul_self_eq_kstar, Language.map, Language.map_kstar, Language.reverse, Language.reverse_reverse, Language.reverse_kstar, Language.reverseIso, RegularExpression.char, RegularExpression.star, RegularExpression.matches'_pow, RegularExpression.deriv_char_self, RegularExpression.deriv_star, RegularExpression.mul_rmatch_iff, RegularExpression.star_rmatch_iff, RegularExpression.map, RegularExpression.matches'_map]
  E1: auto
families: []
requires: [V01.C02, V03.C02, V04.C04, V06.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Languages and regular expressions

### Overview

A formal language is a set of finite words over an alphabet. Examples are the binary numerals, the identifiers of a programming language, or the inputs that a program accepts. The theory of formal languages classifies such sets by the resources that a machine needs to recognize them. The first and smallest class is the class of regular languages. This chapter describes regular languages in three ways: by regular expressions (this section), by finite automata (Section 2), and by the finiteness of the left quotients (the Myhill-Nerode theorem, Section 2). Section 3 goes one step up, to context-free grammars.

This section sets up the algebra. Union, concatenation and the empty word make the languages an idempotent semiring, and the Kleene star makes it a Kleene algebra. A regular expression is a syntax tree that names a language, and Mathlib decides membership with the derivatives of Brzozowski. The main theorems are the star as the union of the powers, Arden's lemma on $X = MX + N$, and the correctness of the derivative algorithm.

### Definitions

**Definition (Word, language).** Let $\alpha$ be a type, the alphabet. A word over $\alpha$ is a finite list $x = [a_1, \dots, a_k]$ of letters, and $|x| = k$ is its length. The empty word is $[\,]$. The concatenation of two words is $x \mathbin{+\!\!+} y$. A language over $\alpha$ is a set of words.

In Mathlib, `Language α` is a definition equal to `Set (List α)`, and it is a complete atomic Boolean algebra.

**Definition (Operations on languages).** Let $l, m$ be languages over $\alpha$.

1. $0 = \varnothing$ and $1 = \{[\,]\}$.
2. $l + m = l \cup m$, and $l - m = l \setminus m$.
3. $l \cdot m = \{x \mathbin{+\!\!+} y : x \in l,\ y \in m\}$, the concatenation.
4. $l^0 = 1$ and $l^{n+1} = l \cdot l^n$.
5. $l^{*}$ is the set of words $y_1 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} y_k$ with $k \geq 0$ and all $y_i \in l$.
6. $l^{R} = \{x : \operatorname{rev}(x) \in l\}$, the reversal, and for $f \colon \alpha \to \beta$, $f(l) = \{f(x) : x \in l\}$, the image under the letter map $f$.

The unit $1$ is not the language of all words, which is the top element $\top$.

**Definition (Regular expression).** The regular expressions over $\alpha$ form the inductive type with six constructors: `zero` (written $0$), `epsilon` (written $1$), `char a` for a letter $a$, `plus P Q` (written $P + Q$), `comp P Q` (written $P \cdot Q$) and `star P`. The language of an expression is defined by recursion: $$L(0) = 0,\quad L(1) = 1,\quad L(a) = \{[a]\},\quad L(P + Q) = L(P) + L(Q),\quad L(P \cdot Q) = L(P)\, L(Q),\quad L(P^{*}) = L(P)^{*}.$$ In Mathlib this is `P.matches'`; the prime is there because `matches` is a keyword.

Section 2 defines regular languages by finite automata. Kleene's theorem says that the languages $L(P)$ are exactly these; the index of this edition has no declaration for this equivalence.

**Definition (Nullability).** The Boolean `matchEpsilon P` is defined by recursion: false for $0$ and for a letter, true for $1$ and for a star, the disjunction for a sum and the conjunction for a product.

**Definition (Derivative).** Let $\alpha$ have decidable equality and let $a \in \alpha$. The derivative $\partial_a P$ is defined by recursion: $$\partial_a 0 = 0,\quad \partial_a 1 = 0,\quad \partial_a b = \begin{cases} 1 & b = a \\ 0 & b \neq a,\end{cases}\quad \partial_a(P + Q) = \partial_a P + \partial_a Q,\quad \partial_a(P^{*}) = (\partial_a P)\cdot P^{*},$$ and $\partial_a (P \cdot Q) = (\partial_a P) \cdot Q + \partial_a Q$ if `matchEpsilon P` is true, and $(\partial_a P)\cdot Q$ if it is false. The matcher is `rmatch P [] = matchEpsilon P` and `rmatch P (a :: x) = rmatch (P.deriv a) x`. The definitions are pure syntax, so `rmatch` runs by `decide`.

### Theorems and proofs

**Proposition (The semiring of languages).** With the operations above, `Language α` is a semiring. Addition is idempotent, $l + l = l$, and $l \leq m$ if and only if $l + m = m$. If $\alpha$ has two distinct letters, the multiplication is not commutative.

*Proof.* Union is associative, commutative and idempotent, with unit $\varnothing$, and $l \subseteq m$ if and only if $l \cup m = m$. Concatenation of words is associative, so $(l m) n$ and $l (m n)$ both consist of the words $x \mathbin{+\!\!+} y \mathbin{+\!\!+} z$ with $x \in l$, $y \in m$, $z \in n$. Since $[\,] \mathbin{+\!\!+} x = x = x \mathbin{+\!\!+} [\,]$, $1$ is a unit. A product with $\varnothing$ has no words, so $0 \cdot m = 0 = m \cdot 0$. A word is in $l (m + n)$ if and only if it is $x \mathbin{+\!\!+} y$ with $x \in l$ and $y \in m \cup n$, that is, if it is in $l m \cup l n$; the right law is the same. Last, let $a \neq b$. Then $\{[a]\}\{[b]\} = \{[a, b]\}$ and $\{[b]\}\{[a]\} = \{[b, a]\}$, and these differ. $\square$

**Proposition (Powers).** A word $x$ is in $l^n$ if and only if there is a list $S$ of $n$ words, each in $l$, whose flattening is $x$.

*Proof.* Induction on $n$. For $n = 0$, $l^0 = 1$ and the empty list flattens to $[\,]$. For the step, $x \in l^{n+1} = l \cdot l^n$ if and only if $x = y \mathbin{+\!\!+} z$ with $y \in l$ and $z \in l^n$. By the hypothesis of induction, $z$ is the flattening of a list $S$ of $n$ members of $l$. Then $x$ is the flattening of $y :: S$, which has length $n + 1$. The converse reads the same steps backward. $\square$

**Theorem (The star is the union of the powers).** For each language $l$, $$l^{*} = \bigcup_{n \geq 0} l^n, \qquad 1 + l \cdot l^{*} = l^{*}, \qquad l^{*} \cdot l = l \cdot l^{*}.$$

*Proof.* A list of members of $l$ has some length $n$, so the proposition on powers gives the first identity. Multiplication distributes over arbitrary unions, by the proof of distributivity above, so $$1 + l \cdot \bigcup_n l^n = l^0 \cup \bigcup_n l^{n+1} = \bigcup_n l^n.$$ For the third, $l^{*} l = \bigcup_n l^n l = \bigcup_n l^{n+1} = \bigcup_n l\, l^n = l\, l^{*}$, because $l^n l = l^{n+1} = l\, l^n$ by associativity. $\square$

Mathlib uses the theorem to make `Language α` a `KleeneAlgebra`. Also, a word is in $l^{*}$ if and only if it is the flattening of a list of nonempty members of $l$: remove the empty words from the list, which does not change the flattening.

**Theorem (Arden's lemma).** Let $l, m, n$ be languages with $[\,] \notin m$. Then $l = m l + n$ if and only if $l = m^{*} n$.

*Proof.* Suppose $l = m^{*} n$. Then $m l + n = (m\, m^{*} + 1) n = m^{*} n = l$, by the right distributive law and the theorem on the star.

Conversely, suppose $l = m l + n$. First, $m^{*} n \subseteq l$. By the theorem on the star, it is enough to prove $m^k n \subseteq l$ for each $k$, by induction on $k$. For $k = 0$, $n \subseteq m l + n = l$. If $m^k n \subseteq l$, then $m^{k+1} n = m (m^k n) \subseteq m l \subseteq l$.

Second, $l \subseteq m^{*} n$. Prove by strong induction on $|x|$ that each $x \in l$ is in $m^{*} n$. Since $l = m l + n$, either $x \in n$ or $x = y \mathbin{+\!\!+} z$ with $y \in m$ and $z \in l$. In the first case, $x = [\,] \mathbin{+\!\!+} x \in m^{*} n$, since $[\,] \in m^{*}$. In the second case, $y \neq [\,]$ because $[\,] \notin m$, so $|z| < |x|$. By the hypothesis of induction, $z \in m^{*} n$, so $x = y \mathbin{+\!\!+} z \in m\, m^{*} n \subseteq m^{*} n$. $\square$

**Proposition (Reversal).** For languages $l, m$: $(l m)^{R} = m^{R} l^{R}$, $(l + m)^{R} = l^{R} + m^{R}$, $(l^{*})^{R} = (l^{R})^{*}$ and $(l^{R})^{R} = l$.

*Proof.* The word $x$ is in $(lm)^R$ if and only if $\operatorname{rev}(x) = y \mathbin{+\!\!+} z$ with $y \in l$, $z \in m$, that is, $x = \operatorname{rev}(z) \mathbin{+\!\!+} \operatorname{rev}(y) \in m^R l^R$. Reversal of words is a bijection, so it commutes with unions. For the star, $(l^n)^R = (l^R)^n$ by induction with the first identity, and the star is the union of the powers. Last, $\operatorname{rev}(\operatorname{rev}(x)) = x$. $\square$

**Lemma (Nullability).** For each regular expression $P$, $[\,] \in L(P)$ if and only if `matchEpsilon P` is true.

*Proof.* Induction on $P$. The empty word is not in $0$ or $\{[a]\}$, and it is in $1$ and in every star. For a sum, take the disjunction. For a product, $y \mathbin{+\!\!+} z = [\,]$ forces $y = z = [\,]$, which gives the conjunction. $\square$

**Theorem (The derivative).** For each regular expression $P$, letter $a$ and word $x$: $$x \in L(\partial_a P) \iff a :: x \in L(P).$$

*Proof.* Induction on $P$, for all $x$ at once.

Cases $0$, $1$ and $P + Q$. For $0$ and $1$ the derivative is $0$, and $a :: x$ is neither in $0$ nor equal to $[\,]$. For a sum, the hypotheses match the two disjunctions.

Case $b$, a letter. The word $a :: x$ equals $[b]$ if and only if $b = a$ and $x = [\,]$, which is $x \in L(\partial_a b)$ in both cases $b = a$ and $b \neq a$.

Case $P \cdot Q$. The word $a :: x$ is in $L(P) L(Q)$ if and only if $a :: x = y \mathbin{+\!\!+} z$ with $y \in L(P)$, $z \in L(Q)$. Either $y = [\,]$, or $y = a :: y'$ and then $x = y' \mathbin{+\!\!+} z$. By the lemma and the hypothesis on $Q$, the first alternative says that `matchEpsilon P` holds and $x \in L(\partial_a Q)$. By the hypothesis on $P$, the second says $x \in L((\partial_a P) \cdot Q)$. The derivative is the sum of the two when `matchEpsilon P` is true, and the second alone when the first alternative is impossible.

Case $P^{*}$. Suppose $a :: x \in L(P)^{*}$. By the remark on nonempty factors, $a :: x = w_1 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} w_k$ with each $w_i \in L(P)$ nonempty. Since the word is nonempty, $k \geq 1$, and $w_1 = a :: y$ for a word $y$. So $x = y \mathbin{+\!\!+} (w_2 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} w_k)$, with $y \in L(\partial_a P)$ by the hypothesis on $P$ and the rest in $L(P)^{*}$. So $x \in L((\partial_a P) \cdot P^{*})$. Conversely, if $x = y \mathbin{+\!\!+} z$ with $a :: y \in L(P)$ and $z \in L(P)^{*}$, then $a :: x = (a :: y) \mathbin{+\!\!+} z \in L(P) \cdot L(P)^{*} \subseteq L(P)^{*}$. $\square$

**Corollary (Correctness of the matcher).** For each $P$ and $x$, `rmatch P x` is true if and only if $x \in L(P)$. In particular, membership in $L(P)$ is decidable.

*Proof.* Induction on $x$, for all $P$. For $x = [\,]$, `rmatch P []` is `matchEpsilon P`, and the lemma on nullability applies. For $x = a :: x'$, `rmatch P x` is `rmatch (P.deriv a) x'`, which by the hypothesis of induction holds if and only if $x' \in L(\partial_a P)$, and by the theorem on the derivative this is $a :: x' \in L(P)$. $\square$

Mathlib proves the corollary as `rmatch_iff_matches'` by induction on $P$ instead, with lemmas on `rmatch` for a product and a star.

### Examples

**Example (A small star).** Let $\alpha = \{a, b\}$ and $l = \{a, ab\}$. Then $$l^2 = \{aa,\ aab,\ aba,\ abab\},$$ four words. The star $l^{*}$ is the set of words that are empty, or begin with $a$ and contain no factor $bb$. Indeed, each word of $l^{*}$ has this form. Conversely, if $w$ begins with $a$ and has no $bb$, cut $w$ before each $a$; each piece is an $a$ followed by at most one $b$, so it is $a$ or $ab$. For example $abaab = (ab)(a)(ab)$.

**Example (A derivative computation).** Let $P = (a \cdot b)^{*}$ over $\{a, b\}$, so $L(P) = \{[\,], ab, abab, \dots\}$. Compute `rmatch P [a, b]`. First, $\partial_a P = \partial_a(a \cdot b) \cdot P$. Since `matchEpsilon a` is false, $\partial_a (a \cdot b) = (\partial_a a) \cdot b = 1 \cdot b$. So $D_1 = (1 \cdot b) \cdot P$. Next, `matchEpsilon (1 · b)` is `true && false = false`, so $\partial_b D_1 = \partial_b(1 \cdot b) \cdot P$. Since `matchEpsilon 1` is true, $\partial_b(1 \cdot b) = (\partial_b 1)\cdot b + \partial_b b = 0 \cdot b + 1$. So $D_2 = (0 \cdot b + 1) \cdot P$, and `matchEpsilon D₂` is `(false || true) && true = true`. The word $ab$ is accepted. For the word $aa$, the second step gives $\partial_a(1 \cdot b) = 0 \cdot b + 0$, which is not nullable, so the product with $P$ is not nullable and $aa$ is rejected. The expressions grow, because Mathlib does not simplify $0 \cdot b$ to $0$.

**Example (Arden's lemma).** Over $\{a, b\}$, the equation $X = \{a\} X + \{b\}$ has the unique solution $X = \{a\}^{*}\{b\} = \{b, ab, aab, \dots\}$, because $[\,] \notin \{a\}$. This is how a regular expression is read off an automaton: each state gives one equation, and the lemma removes the unknowns one by one.

**Counterexample (Arden's lemma without the hypothesis).** Let $m = 1$ and $n = 0$. Then $m l + n = l$ for every $l$, so every language solves the equation, but $m^{*} n = 0$. The hypothesis $[\,] \notin m$ is what makes the solution unique.

### The library around it

::: mathlib
`Language` · `Mathlib.Computability.Language`

`Language α` is `Set (List α)`, with membership, `{x}` and `insert`. The membership lemmas are `mem_add`, `mem_one`, `mem_mul : x ∈ l * m ↔ ∃ a ∈ l, ∃ b ∈ m, a ++ b = x`, `mem_inf`, `mem_pow` and `mem_kstar`. `mem_kstar_iff_exists_nonempty` adds the condition `y ≠ []` to each factor, and `nil_mem_kstar` gives the empty word. The instances are `instSemiring`, the complete atomic Boolean algebra, and `instKleeneAlgebra`; `add_self` and `le_iff : l ≤ m ↔ l + m = m` record that addition is the join.

<?decl Language?>
:::

::: mathlib
`Language.kstar_eq_iSup_pow` · `Mathlib.Computability.Language`

`kstar_eq_iSup_pow l : l∗ = ⨆ i : ℕ, l ^ i` is the theorem on the star. Its corollaries are `one_add_self_mul_kstar_eq_kstar : 1 + l * l∗ = l∗`, `one_add_kstar_mul_self_eq_kstar` and `mul_self_kstar_comm : l∗ * l = l * l∗`. `Language.map f` is a ring homomorphism `Language α →+* Language β`, and `map_kstar` says that it commutes with the star.

<?decl Language.kstar_eq_iSup_pow?>
:::

::: mathlib
`Language.self_eq_mul_add_iff` · `Mathlib.Computability.Language`

Arden's lemma: `self_eq_mul_add_iff (hm : [] ∉ m) : l = m * l + n ↔ l = m∗ * n`.

<?decl Language.self_eq_mul_add_iff?>
:::

::: mathlib
`Language.reverse` · `Mathlib.Computability.Language`

`l.reverse` is `{w | w.reverse ∈ l}`. The lemmas include `reverse_reverse`, `reverse_mul : (l * m).reverse = m.reverse * l.reverse` and `reverse_kstar`. `reverseIso : Language α ≃+* (Language α)ᵐᵒᵖ` packages reversal as a ring isomorphism to the opposite ring.

<?decl Language.reverse?>
:::

::: mathlib
`RegularExpression` · `Mathlib.Computability.RegularExpressions`

The inductive type `RegularExpression α` has the constructors `zero`, `epsilon`, `char`, `plus`, `comp` and `star`, with the notations `0`, `1`, `+`, `*` and `P ^ n`. `P.matches' : Language α` is the language, with `matches'_pow` for powers. `map f` changes the alphabet, and `matches'_map` says that the language of the image is the image of the language.

<?decl RegularExpression?>
:::

::: mathlib
`RegularExpression.rmatch_iff_matches'` · `Mathlib.Computability.RegularExpressions`

Under `[DecidableEq α]`, `deriv P a` is the derivative, with the simp lemmas `deriv_char_self`, `deriv_star` and the others, and `rmatch : RegularExpression α → List α → Bool` is the matcher. `rmatch_iff_matches' P x : P.rmatch x ↔ x ∈ P.matches'` is its correctness, proved with `mul_rmatch_iff` and `star_rmatch_iff`; it gives the instance `DecidablePred (· ∈ P.matches')`.

<?decl RegularExpression.rmatch_iff_matches'?>
:::

Common errors of a learner: The first error is to type the star of a language with the ASCII `*`; the star is `∗` (U+2217, `\ast`), and `l * l` is a product. The second error is to read `1 : Language α` as the full language; it is `{[]}`, and the full language is `⊤`. The third error is to expect `P + P = P` for regular expressions; equality of expressions is equality of syntax trees. The fourth error is to call `deriv` or `rmatch` on an alphabet without `DecidableEq`; the derivative of `char a` compares letters.

### Exercises

1. (A) Over $\{a, b\}$, list the words of length at most $4$ in $\{a, ab\}^{*}$, and check the description of the example. Hint: there are $1 + 1 + 2 + 3 + 5$ of them, a Fibonacci pattern.
2. (A) Compute `rmatch ((a + b)* · a · b) [b, a, b]` by hand with the derivative. Hint: at each step record whether the left factor is nullable.
3. (A) Show that $(l^{*})^{*} = l^{*}$ and $l^{*} l^{*} = l^{*}$. Hint: use the description by lists of words; a list of lists flattens to a list.
4. (B) Use Arden's lemma to find the language $X$ over $\{a, b\}$ with $X = \{b\} X + \{a\}$, and describe it in words. Then solve the system $X = \{a\} Y + 1$, $Y = \{b\} X$ by substitution. Hint: the first answer is $\{b\}^{*}\{a\}$; for the system, substitute $Y$ and get $X = \{ab\} X + 1$.
5. (B) Define the reversal $\operatorname{rev}(P)$ of a regular expression by recursion, with $\operatorname{rev}(P \cdot Q) = \operatorname{rev}(Q) \cdot \operatorname{rev}(P)$ and the other constructors unchanged on the outside. Prove $L(\operatorname{rev} P) = L(P)^{R}$. Hint: induction on $P$, with the proposition on reversal in each case.
6. (B) Prove that $L(P)$ is closed under the map of the alphabet: $L(P.\mathrm{map}\, f) = f(L(P))$. Hint: induction on $P$; for the star, use that the image map is a ring homomorphism that commutes with the star.
7. (C) Prove that for a fixed $P$ the set $\{\partial_w P : w \in \alpha^{*}\}$ of iterated derivatives is finite up to the identities $R + R = R$, $R + S = S + R$ and $(R + S) + T = R + (S + T)$. Deduce that each language $L(P)$ has finitely many left quotients. Hint: this is Brzozowski's theorem; prove by induction on $P$ that the derivatives of $P \cdot Q$ are sums of a derivative of $P$ times $Q$ and of derivatives of $Q$.

### Notes and history

Kleene introduced regular events, now called regular expressions, in 1956, and proved that they describe the sets recognized by finite automata. Brzozowski introduced the derivative of a regular expression in 1964 and used it to build automata from expressions; the matcher `rmatch` is his algorithm without the step that identifies similar expressions. Arden's lemma is named after D. N. Arden, who used it to solve systems of equations between languages.

The Mathlib files are by these authors, read from their headers: `Mathlib.Computability.Language` by Fox Thomson, Martin Dvorak and Rudy Peterson, and `Mathlib.Computability.RegularExpressions` by Fox Thomson.

### Reference

<?reference?>
