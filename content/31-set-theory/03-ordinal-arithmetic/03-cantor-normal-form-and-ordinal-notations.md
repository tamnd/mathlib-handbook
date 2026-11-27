---
title: Cantor normal form and ordinal notations
kind: theory
modules:
  - Mathlib.SetTheory.Ordinal.CantorNormalForm
  - Mathlib.SetTheory.Ordinal.Notation
explains:
  E3: [Ordinal.CNF, Ordinal.CNF.coeff, ONote, ONote.NF, NONote]
  E2: [Ordinal.CNF.ne_zero, Ordinal.CNF.opow_mul_add, Ordinal.CNF.foldr, Ordinal.CNF.snd_pos, Ordinal.CNF.snd_lt, Ordinal.CNF.sortedGT, Ordinal.CNF.eval, Ordinal.CNF.eval_coeff, Ordinal.CNF.coeff_eval, Ordinal.CNF.of_le_one, ONote.repr, ONote.NFBelow, ONote.cmp, ONote.repr_inj, ONote.lt_def, ONote.repr_add, ONote.repr_mul, ONote.repr_opow, ONote.fundamentalSequence, ONote.fastGrowing]
  E1: auto
families: []
requires: [V04.C01, V31.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Cantor normal form and ordinal notations

### Overview

Each natural number has a unique expansion in base $10$. Each ordinal has a unique expansion in a base $b > 1$, with exponents that are ordinals: this is the Cantor normal form. It is the base-$b$ division of Section 2, repeated. In base $\omega$ the coefficients are natural numbers, and the exponents can again be expanded. Below the ordinal $\varepsilon_0$ this process stops after finitely many steps, so each ordinal below $\varepsilon_0$ is a finite tree of natural numbers. Mathlib uses these trees as a data type `ONote` with computable addition, multiplication and powers. The section proves the normal form theorem, shows that the notations describe exactly the ordinals below $\varepsilon_0$, and ends with the fundamental sequences and the fast growing hierarchy that Mathlib defines on them.

### Definitions

**Definition (Cantor normal form).** Let $b > 1$. A *base-$b$ normal form* of $\alpha$ is an expression
$$\alpha = b^{e_1} c_1 + b^{e_2} c_2 + \cdots + b^{e_k} c_k, \qquad e_1 > e_2 > \cdots > e_k, \qquad 0 < c_i < b,$$
with $k \ge 0$. The empty sum, $k = 0$, is the form of $0$.

::: mathlib
`Ordinal.CNF` · `Mathlib.SetTheory.Ordinal.CantorNormalForm`

`CNF b o : List (Ordinal × Ordinal)` is the list of the pairs $(e_i, c_i)$. It is defined by the recursion `CNF.rec` on `o`, which steps from `o ≠ 0` to `o % b ^ log b o`; the lemma `CNF.ne_zero` gives `CNF b o = (log b o, o / b ^ log b o) :: CNF b (o % b ^ log b o)`. So the definition makes sense for all `b`, and `CNF.of_le_one` gives the junk value `CNF b o = [(0, o)]` for `b ≤ 1` and `o ≠ 0`. The properties of the theorem below are `CNF.foldr` (the sum is `o`), `CNF.snd_pos`, `CNF.snd_lt (hb : 1 < b)` and `CNF.sortedGT` (the exponents decrease). `CNF.opow_mul_add` computes the form of `b ^ e * x + y`.

<?decl Ordinal.CNF?>
:::

::: mathlib
`Ordinal.CNF.coeff` · `Mathlib.SetTheory.Ordinal.CantorNormalForm`

`CNF.coeff b o : Ordinal →₀ Ordinal` sends each exponent $e$ to its coefficient, and to `0` if $e$ does not occur. `CNF.eval b f` evaluates a finitely supported function as a sum in decreasing order of the exponents. Then `eval_coeff b o : eval b (coeff b o) = o`, and `coeff_eval (hb : 1 < b) (hf : ∀ e, f e < b) : coeff b (eval b f) = f` is the uniqueness. The form as a function suits comparisons and sums: `coeff_injective b` says that the coefficients determine the ordinal.

<?decl Ordinal.CNF.coeff?>
:::

**Definition (Ordinal notations).** The *ordinal notations* are the terms of the inductive type with a constant $0$ and a constructor $\operatorname{oadd}(e, n, a)$ for notations $e, a$ and a positive natural number $n$. The *value* is
$$\operatorname{repr}(0) = 0, \qquad \operatorname{repr}(\operatorname{oadd}(e, n, a)) = \omega^{\operatorname{repr}(e)} \cdot n + \operatorname{repr}(a).$$
A notation is in *normal form* if it is $0$, or it is $\operatorname{oadd}(e, n, a)$ with $e$ and $a$ in normal form and $\operatorname{repr}(a) < \omega^{\operatorname{repr}(e)}$,.

**Definition ($\varepsilon_0$).** Let $t_0 = 0$ and $t_{n+1} = \omega^{t_n}$. Set $\varepsilon_0 = \sup_n t_n$.

So $t_1 = 1$, $t_2 = \omega$, $t_3 = \omega^\omega$, and $\varepsilon_0$ is the limit of the towers $\omega^{\omega^{\cdot^{\cdot^\omega}}}$. By normality of $\omega^{\cdot}$, $\omega^{\varepsilon_0} = \sup_n t_{n+1} = \varepsilon_0$. Chapter 4 shows that $\varepsilon_0$ is the least $\alpha$ with $\omega^\alpha = \alpha$, and defines the general $\varepsilon_\alpha$.

::: mathlib
`ONote` · `Mathlib.SetTheory.Ordinal.Notation`

`ONote` has the constructors `zero` and `oadd : ONote → ℕ+ → ONote → ONote`, and `repr : ONote → Ordinal.{0}` is the value. The order is pulled back by `repr` (`ONote.lt_def : x < y ↔ repr x < repr y`), so `ONote` is only a preorder: two terms with the same value are not equal. `ONote.cmp` compares two terms by structure, first the exponents, then the coefficients, then the tails, and it is correct for normal forms. Addition `ONote.add`, subtraction, multiplication `ONote.mul` and the power `ONote.opow` are recursive functions on the terms.

<?decl ONote?>
:::

::: mathlib
`ONote.NF` · `Mathlib.SetTheory.Ordinal.Notation`

`NF o` is a class: it says that `NFBelow o b` holds for some `b`, where `NFBelow o b` is the inductive form of "`o` is in normal form and `repr o < ω ^ b`". `NFBelow.repr_lt` gives that bound. Instances prove `NF` for sums, products and powers of normal forms, and `ONote.decidableNF` decides it. The lemmas `repr_inj [NF a] [NF b] : repr a = repr b ↔ a = b`, `repr_add`, `repr_mul` and `repr_opow` all take `NF` hypotheses.

<?decl ONote.NF?>
:::

### Theorems and proofs

**Lemma (Bound on a normal form).** Let $b > 1$, $e_1 > \cdots > e_k$ and $c_i < b$. Then $\sum_i b^{e_i} c_i < b^{e_1 + 1}$.

*Proof.* Induction on $k$. For $k = 1$, $b^{e_1} c_1 < b^{e_1} b = b^{e_1 + 1}$. For $k > 1$, let $\rho$ be the sum of the terms after the first. The hypothesis of induction gives $\rho < b^{e_2 + 1} \le b^{e_1}$, since $e_2 + 1 \le e_1$. So the sum is less than $b^{e_1} c_1 + b^{e_1} = b^{e_1}(c_1 + 1) \le b^{e_1} b = b^{e_1 + 1}$. $\square$

**Theorem (Cantor normal form).** Let $b > 1$. Each ordinal $\alpha$ has exactly one base-$b$ normal form.

*Proof.* Existence, by induction on $\alpha$. The case $\alpha = 0$ is the empty sum. For $\alpha \neq 0$, Section 2 gives $\alpha = b^c q + r$ with $c = \log_b \alpha$, $0 < q < b$ and $r < b^c \le \alpha$. By induction, $r$ has a normal form. Its exponents $e$ satisfy $b^e \le r < b^c$, so $e < c$. Put $b^c q$ in front.

Uniqueness, by induction on $\alpha$. Take a normal form of $\alpha \neq 0$ with leading term $b^{e_1} c_1$ and the rest $\rho$. Then $b^{e_1} \le \alpha$, and $\alpha < b^{e_1 + 1}$ by the lemma, so $e_1 = \log_b \alpha$. The lemma also gives $\rho < b^{e_1}$. By the uniqueness of the division of $\alpha$ by $b^{e_1}$ (Section 1), $c_1$ and $\rho$ are determined by $\alpha$. As $\rho < \alpha$, the induction gives that the rest of the form is determined too. $\square$

The proof is the recursion of `Ordinal.CNF`, and its uniqueness part is `CNF.coeff_eval`.

**Theorem (Notations describe $\varepsilon_0$).** The map $\operatorname{repr}$ sends the notations in normal form onto $\varepsilon_0 = \{\alpha : \alpha < \varepsilon_0\}$, and it is injective on them.

*Proof.* The values are below $\varepsilon_0$. Use induction on the term. $\operatorname{repr}(0) = 0 < \varepsilon_0$. Let $o = \operatorname{oadd}(e, n, a)$ be in normal form, so $\operatorname{repr}(a) < \omega^{\operatorname{repr}(e)}$. By induction, $\operatorname{repr}(e) < t_k$ for some $k$. Then
$$\operatorname{repr}(o) < \omega^{\operatorname{repr}(e)} (n + 1) < \omega^{\operatorname{repr}(e) + 1} \le \omega^{t_k} = t_{k+1} < \varepsilon_0,$$
where $\omega^{\operatorname{repr}(e)} \cdot \omega = \omega^{\operatorname{repr}(e) + 1}$ and $n + 1 < \omega$ give the second inequality.

Each $\alpha < \varepsilon_0$ is a value. First, no $\alpha < \varepsilon_0$ satisfies $\omega^\alpha = \alpha$: by induction on $k$, if $\omega^\alpha = \alpha < t_{k+1} = \omega^{t_k}$, then $\alpha < t_k$ by strict monotonicity, and $\alpha < t_0 = 0$ is impossible. Now use induction on $\alpha$. Write $\alpha$ in base-$\omega$ normal form with exponents $e_1 > \cdots > e_k$ and natural coefficients $c_i > 0$. Then $e_1 \le \omega^{e_1} \le \alpha$. If $e_1 = \alpha$, then $\omega^\alpha \le \alpha \le \omega^\alpha$, and $\alpha$ is a fixed point. So $e_i \le e_1 < \alpha$. By induction, each $e_i$ is $\operatorname{repr}(\hat e_i)$ for a notation $\hat e_i$ in normal form. The term $\operatorname{oadd}(\hat e_1, c_1, \operatorname{oadd}(\hat e_2, c_2, \ldots, \operatorname{oadd}(\hat e_k, c_k, 0)))$ is in normal form, by the lemma, and its value is $\alpha$.

Injectivity. The structure of a normal form term is the base-$\omega$ normal form of its value, by the lemma, and this form is unique. Induction on the terms gives that two normal terms with the same value are equal. $\square$

The index of this edition has no declaration for the first two statements of the theorem: there is no lemma `repr o < ε₀` and no lemma that each ordinal below $\varepsilon_0$ is a value. Mathlib has the injectivity as `ONote.repr_inj`, and the module documentation describes `NONote` as the ordinals below $\varepsilon_0$.

**Proposition (Addition of notations).** For $o = \operatorname{oadd}(e, n, a)$ and a normal $p$, write the normal form of $a + p$ as $\operatorname{oadd}(e', n', a')$ or $0$. Then $o + p$ is $\operatorname{oadd}(e, n, 0)$ if $a + p = 0$, and otherwise is $a + p$ if $e < e'$, $\operatorname{oadd}(e, n + n', a')$ if $e = e'$, and $\operatorname{oadd}(e, n, a + p)$ if $e > e'$.

*Proof.* The value of $o + p$ is $\omega^{e} n + (a + p)$ by associativity, with $a + p = \omega^{e'} n' + a'$. Let $e < e'$ and $\delta = e' - e \ge 1$. Then $\omega \le \omega^\delta$, so $\omega^\delta = \omega + \gamma$ for some $\gamma$, and $n + \omega^\delta = (n + \omega) + \gamma = \omega^\delta$. So $\omega^e n + \omega^{e'} = \omega^e (n + \omega^\delta) = \omega^{e'}$, and the term $\omega^e n$ is absorbed by the first copy of $\omega^{e'}$ in $\omega^{e'} n'$. If $e = e'$, the left distributive law gives $\omega^e (n + n') + a'$. If $e > e'$, the expression is already in normal form. $\square$

This is the function `ONote.addAux` behind `ONote.add`, and `repr_add` is its correctness.

### Examples

**Example (Absorption).** In base $\omega$, $\omega \cdot 3 + \omega^2 = \omega (3 + \omega) = \omega^2$. The notation computes the same value: `oadd 1 3 0 + oadd 2 1 0` reduces to `addAux 1 3 (oadd 2 1 0)`, and `cmp 1 2 = lt` gives `oadd 2 1 0`. In the other order, $\omega^2 + \omega \cdot 3$ is already a normal form.

**Example (A product).** The function `ONote.mul` uses the rule
$$\operatorname{oadd}(e_1, n_1, a_1) \cdot \operatorname{oadd}(e_2, n_2, a_2) = \begin{cases} \operatorname{oadd}(e_1, n_1 n_2, a_1) & \text{if } e_2 = 0, \\ \operatorname{oadd}(e_1 + e_2, n_2, o_1 \cdot a_2) & \text{otherwise,} \end{cases}$$
where $o_1$ is the left factor. For $(\omega + 1)(\omega + 1)$: the second factor has $e_2 = 1$, so the product is $\operatorname{oadd}(2, 1, (\omega + 1) \cdot 1)$, and $(\omega + 1) \cdot 1 = \omega + 1$ by the first case. The result is $\omega^2 + \omega + 1$. By hand: $(\omega + 1)(\omega + 1) = (\omega + 1)\omega + \omega + 1 = \omega^2 + \omega + 1$, since $(\omega + 1) \omega = \sup_n (\omega n + 1) = \omega^2$.

**Counterexample (The hypothesis `NF`).** The term $o = \operatorname{oadd}(0, 1, \operatorname{oadd}(1, 1, 0))$ denotes $1 + \omega = \omega$, but it is not in normal form. The term $\operatorname{oadd}(1, 1, 0)$ denotes $\omega$ too. So `repr` is not injective without `NF`. The algorithms fail too. The rule for products gives $o \cdot \operatorname{oadd}(1, 1, 0) = \operatorname{oadd}(0 + 1, 1, o \cdot 0) = \operatorname{oadd}(1, 1, 0)$, with value $\omega$. But $\omega \cdot \omega = \omega^2$. So `repr_mul` is false without its `NF` hypotheses.

**Example (Fundamental sequences and fast growth).** For a limit notation $\lambda$, `ONote.fundamentalSequence` gives a sequence $\lambda[i]$ that increases to $\lambda$. For example $\omega[i] = i + 1$ and $\omega^{\alpha + 1}[i] = \omega^\alpha (i + 1)$. The fast growing hierarchy `ONote.fastGrowing` sets $f_0(n) = n + 1$, $f_{\alpha + 1}(n) = f_\alpha^{n}(n)$ and $f_\lambda(n) = f_{\lambda[n]}(n)$. Then $f_1(n) = 2n$ and $f_2(n) = 2^n n$ (`fastGrowing_one`, `fastGrowing_two`). `ONote.fastGrowingε₀` uses the towers $t_i$ as the sequence for $\varepsilon_0$, and `fastGrowingε₀_two` computes $f_{t_2}(2) = f_\omega(2) = f_3(2) = f_2(f_2(2)) = f_2(8) = 2^8 \cdot 8 = 2048$.

::: mathlib
`NONote` · `Mathlib.SetTheory.Ordinal.Notation`

`NONote` is the subtype `{o : ONote // NF o}`. On it the order is linear (`NONote` has a `LinearOrder` instance by `cmp`) and well-founded (`NONote.lt_wf`). `NONote.mk` builds an element from a term with an `NF` instance, `NONote.oadd` is a constructor with the proof obligation `below a e`, and `NONote.recOn` is the induction principle. The operations `+`, `-`, `*` and `NONote.opow` come with `repr_add`, `repr_sub`, `repr_mul` and `repr_opow` and need no hypothesis.

<?decl NONote?>
:::

### The library around it

Both files describe the same normal form in two ways. `Ordinal.CNF` works for all ordinals and all bases, and is not computable, since it uses `log`. `ONote` covers base $\omega$ below $\varepsilon_0$ only, and it computes: `#eval` evaluates `cmp`, `+` and `*` on terms. The ordinal $\varepsilon_0$ itself is `Ordinal.epsilon 0` in `Mathlib.SetTheory.Ordinal.Veblen`, which Chapter 4 treats. The index has no lemma that links `ONote.repr` with it.

Common errors of a learner:

- `CNF b o` lists pairs `(exponent, coefficient)`, with the largest exponent first.
- `CNF 1 o = [(0, o)]`: for bases `b ≤ 1` the list is junk, and the lemmas on coefficients need `1 < b`.
- `x < y` on `ONote` compares values. `x = y` compares terms. Use `NONote` or `repr_inj` with `NF`.
- `repr` lands in `Ordinal.{0}`, the ordinals of the lowest universe.

### Exercises

1. (A) Write the base-$\omega$ normal forms of $(\omega + 2)^2$, $\omega^3 + \omega \cdot 5 + \omega^2$ and $(\omega^\omega + 1)\cdot\omega$.
2. (A) Write the base-$2$ normal form of $\omega + 5$ and of $\omega^2$. Hint: $2^\omega = \omega$.
3. (A) Compute the notation of $(\omega^2 + 3) \cdot (\omega + 2)$ with the rule for products, and check it by hand.
4. (B) Show that $\omega^{\alpha} n + \omega^{\beta} m = \omega^\beta m$ when $\alpha < \beta$ and $n < \omega$.
5. (B) Show that for normal forms, the comparison of values is the lexicographic comparison of the lists of pairs, with exponents first. This is the correctness of `ONote.cmp`.
6. (B) Show that $f_\omega(3) = f_3^{3}(3)$ and that it is greater than $2^{2^{16}}$. Hint: $\omega[3] = 4$ and $f_2(24) = 2^{24} \cdot 24$.
7. (C) Give an algorithm for $\alpha^\beta$ on normal forms when $\beta < \omega$, and prove that it is correct.
8. (C) Show that the ordinals below $\varepsilon_0$ with the operations $+$ and $\cdot$ form a countable structure, and give an injection into $\mathbb{N}$ from the notations.

### Notes and history

Cantor proved the normal form theorem in Part II of the *Beiträge* (1897). The ordinal $\varepsilon_0$ is the proof-theoretic ordinal of Peano arithmetic, by the consistency proof of Gentzen (1936). The fast growing hierarchy is the Löb and Wainer hierarchy, and $f_{\varepsilon_0}$ eventually dominates each function that Peano arithmetic proves total. This section only computes small values.

### Reference

<?reference?>
