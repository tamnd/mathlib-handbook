---
title: Undecidability, reductions and Turing degrees
kind: theory
modules:
  - Mathlib.Computability.Halting
  - Mathlib.Computability.RE
  - Mathlib.Computability.Reduce
  - Mathlib.Computability.RecursiveIn
  - Mathlib.Computability.TuringDegree
explains:
  E3: [ComputablePred, REPred, ComputablePred.computable_iff_re_compl_re, Partrec.merge, ComputablePred.rice, ComputablePred.rice₂, ComputablePred.halting_problem, ComputablePred.halting_problem_re, ComputablePred.halting_problem_not_re, ManyOneReducible, OneOneReducible, ComputablePred.computable_of_manyOneReducible, ManyOneDegree, Nat.RecursiveIn, RecursiveIn, TuringReducible, TuringDegree]
  E2: [ComputablePred.computable_iff, ComputablePred.to_re, ComputablePred.not, Partrec.dom_re, ComputablePred.computable_iff_re_compl_re', Partrec.merge', Computable.find, ComputablePred.ite, PrimrecPred.computablePred, manyOneReducible_refl, ManyOneReducible.trans, OneOneReducible.to_many_one, ManyOneEquiv, OneOneEquiv, OneOneReducible.disjoin_left, disjoin_le, ManyOneDegree.of, ManyOneDegree.add_le, ManyOneDegree.instSemilatticeSup, Nat.Partrec.recursiveIn, RecursiveIn.mono, Nat.RecursiveIn.subst, RecursiveIn.partrec_of_oracle, recursiveIn_empty_iff, partrec_iff_forall_recursiveIn_singleton, TuringReducible.refl, TuringReducible.trans, TuringEquivalent, TuringEquivalent.equivalence, Partrec.turingReducible, TuringReducible.partrec_of_const, partrec_iff_forall_turingReducible, TuringDegree.instPartialOrder]
  E1: auto
families: []
requires: [V01.C01, V04.C01, V03.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Undecidability, reductions and Turing degrees

### Overview

A predicate is decidable in the sense of computability when an algorithm answers each instance with yes or no. The previous section gives the tools to show that some natural predicates are not decidable. The halting problem asks whether a program stops on a given input. Turing proved in 1936 that no algorithm decides it. Rice's theorem extends this: no nontrivial property of the function that a program computes is decidable.

Between decidable and arbitrary predicates lie the recursively enumerable predicates. A predicate is recursively enumerable when an algorithm confirms each yes instance, but may run forever on a no instance. The halting problem is recursively enumerable, and its complement is not. Post's theorem says that a predicate is decidable exactly when it and its complement are recursively enumerable.

Reductions compare the difficulty of problems. A many-one reduction translates instances of one problem into instances of another by a computable function. A Turing reduction allows the use of the second problem as an oracle any number of times. Each kind of reduction gives an order on degrees. The section ends with the Turing degrees, the central object of classical recursion theory.

### Definitions

**Definition (Computable predicate).** Let $\alpha$ be primcodable. A predicate $p$ on $\alpha$ is computable if it is decidable and the function $a \mapsto \mathrm{decide}(p\,a) : \alpha \to \mathrm{Bool}$ is computable.

Equivalently, $p$ is computable when there is a computable $f : \alpha \to \mathrm{Bool}$ with $p\,a \iff f(a) = \mathrm{true}$.

**Definition (Recursively enumerable predicate).** A predicate $p$ on $\alpha$ is recursively enumerable (r.e.) if the partial function $a \mapsto [\text{if } p\,a \text{ then } () \text{ else undefined}]$ is partial recursive.

In Mathlib the partial function is `Part.assert (p a) fun _ => Part.some ()`. Its domain at $a$ is the proposition $p\,a$. The definition needs no decidability: the partial function is a semi-decision procedure that stops exactly on the yes instances. For each partial recursive $f$, the domain $\{a \mid f(a) \text{ is defined}\}$ is r.e.

**Definition (Many-one and one-one reductions).** Let $p$ be a predicate on $\alpha$ and $q$ a predicate on $\beta$. Then $p \leq_0 q$ ($p$ is many-one reducible to $q$) if there is a computable $f : \alpha \to \beta$ with $p\,a \iff q(f a)$ for all $a$. If $f$ is also injective, $p \leq_1 q$ ($p$ is one-one reducible to $q$). The predicates are many-one equivalent if $p \leq_0 q$ and $q \leq_0 p$, and similarly for one-one equivalence.

**Definition (Many-one degree).** A many-one degree is a class of subsets of $\mathbb{N}$ under many-one equivalence. The degrees are ordered by $[p] \leq [q] \iff p \leq_0 q$, and the sum $[p] + [q]$ is the degree of the join $p \oplus q = \{2a \mid a \in p\} \cup \{2b + 1 \mid b \in q\}$.

**Definition (Recursive in a set of oracles).** Let $O$ be a set of partial functions $\mathbb{N} \to \mathrm{Part}\ \mathbb{N}$. The predicate $\mathrm{RecursiveIn}\ O$ is the least predicate that contains zero, the successor, the two projections and each $g \in O$, and that is closed under pairing, composition, primitive recursion and unbounded search.

So the functions recursive in $O$ are the partial recursive functions with the extra basic functions of $O$. An oracle is a black box: a computation may ask it for $g(n)$ and receive the answer in one step, or wait forever if $g(n)$ is undefined.

**Definition (Turing reducibility and Turing degrees).** For partial functions $f, g : \mathbb{N} \to \mathrm{Part}\ \mathbb{N}$, $f \leq_T g$ ($f$ is Turing reducible to $g$) if $f$ is recursive in $\{g\}$. The functions are Turing equivalent, $f \equiv_T g$, if $f \leq_T g$ and $g \leq_T f$. A Turing degree is a class of Turing equivalent partial functions, ordered by $\leq_T$.

### Theorems and proofs

**Proposition (Closure of computable predicates).** If $p$ is computable, then $\neg p$ is computable and $p$ is r.e. A predicate many-one reducible to a computable predicate is computable.

*Proof.* For the negation, compose the computable map $a \mapsto \mathrm{decide}(p\,a)$ with the primitive recursive $\mathrm{not} : \mathrm{Bool} \to \mathrm{Bool}$. For the second claim, the partial function $a \mapsto [\text{if } \mathrm{decide}(p\,a) \text{ then } () \text{ else undefined}]$ is the composition of a computable function with the partial function on $\mathrm{Bool}$ that is $()$ at $\mathrm{true}$ and undefined at $\mathrm{false}$. For the third claim, let $p\,a \iff q(f a)$ with $f$ computable. Then $a \mapsto \mathrm{decide}(q(f a))$ is the composition of $f$ and the decision function of $q$, and it decides $p$. $\square$

**Lemma (Merge).** Let $f, g : \alpha \to \mathrm{Part}\ \sigma$ be partial recursive. There is a partial recursive $k$ such that $k(a)$ is defined if and only if $f(a)$ or $g(a)$ is defined, and each value of $k(a)$ is a value of $f(a)$ or of $g(a)$. If $f$ and $g$ agree where both are defined, then $x \in k(a) \iff x \in f(a) \lor x \in g(a)$.

*Proof.* Take codes $c_f$ and $c_g$. Use the bounded evaluation of the previous section and define, for each $n$, the option value $h(a, n)$: the value of $\mathrm{evaln}\ n\ c_f\ a$ if it is $\mathrm{some}$, else the value of $\mathrm{evaln}\ n\ c_g\ a$. This $h$ is primitive recursive. Let $k(a) = \mathrm{rfindOpt}(n \mapsto h(a, n))$. If $f(a)$ is defined, then $\mathrm{evaln}\ n\ c_f\ a$ is $\mathrm{some}$ for large $n$, so the search stops; the same holds for $g$. Conversely, a value of the search is a value of a bounded evaluation, hence a value of $f(a)$ or of $g(a)$ by soundness. The last claim follows when the values agree. $\square$

The proof runs both computations in parallel, one step of each in turn. This is dovetailing, and it is the reason r.e. predicates are closed under disjunction.

**Theorem (Post).** A predicate $p$ is computable if and only if $p$ and $\neg p$ are both r.e.

*Proof.* If $p$ is computable, then $\neg p$ is computable, and both are r.e. by the proposition. Conversely, let $p$ and $\neg p$ be r.e. Mathlib states this direction with a decidability instance on $p$, or classically in a second form. Let $f(a)$ be $\mathrm{true}$ when the semi-decision procedure for $p$ stops on $a$, and undefined otherwise. Let $g(a)$ be $\mathrm{false}$ when the procedure for $\neg p$ stops, and undefined otherwise. Both are partial recursive, and they are never both defined, because $p\,a$ and $\neg p\,a$ do not hold together. The merge lemma gives a partial recursive $k$ with $x \in k(a) \iff x \in f(a) \lor x \in g(a)$. For each $a$, either $p\,a$ or $\neg p\,a$ holds, so $k(a)$ is defined, and $k(a) = \mathrm{decide}(p\,a)$. A total partial recursive function is computable. $\square$

**Theorem (Rice).** Let $C$ be a set of partial functions $\mathbb{N} \to \mathrm{Part}\ \mathbb{N}$, and suppose that the predicate $c \mapsto \mathrm{eval}\ c \in C$ on codes is computable. If $f$ and $g$ are partial recursive and $f \in C$, then $g \in C$.

*Proof.* Define $F(c, n) = g(n)$ if $\mathrm{eval}\ c \in C$, and $F(c, n) = f(n)$ otherwise. Since the test $\mathrm{eval}\ c \in C$ is computable and $f, g$ are partial recursive, $F$ is partial recursive in two arguments. The second recursion theorem gives a code $c$ with $\mathrm{eval}\ c = F(c, \cdot)$. If $\mathrm{eval}\ c \in C$, then $\mathrm{eval}\ c = g$, so $g \in C$. If $\mathrm{eval}\ c \notin C$, then $\mathrm{eval}\ c = f$, and $f \in C$ gives $\mathrm{eval}\ c \in C$, a contradiction. So $g \in C$. $\square$

**Corollary (Rice, for sets of codes).** Let $C$ be a set of codes that is extensional: if $\mathrm{eval}\ c = \mathrm{eval}\ d$, then $c \in C \iff d \in C$. Then $C$ is computable if and only if $C = \emptyset$ or $C$ is the set of all codes.

*Proof.* The empty set and the full set are decided by constant functions. Conversely, let $C$ be computable and nonempty, with $c_0 \in C$. By extensionality, $c \in C \iff \mathrm{eval}\ c \in \mathrm{eval}(C)$, so the predicate $c \mapsto \mathrm{eval}\ c \in \mathrm{eval}(C)$ is computable. For each code $d$, apply the theorem to $f = \mathrm{eval}\ c_0$ and $g = \mathrm{eval}\ d$, which are partial recursive. It gives $\mathrm{eval}\ d \in \mathrm{eval}(C)$, so $d \in C$. $\square$

**Theorem (Halting problem).** For each $n \in \mathbb{N}$, the predicate "$\mathrm{eval}\ c\ n$ is defined" on codes $c$ is r.e. but not computable. Its negation is not r.e.

*Proof.* The predicate is the domain of the partial recursive function $c \mapsto \mathrm{eval}\ c\ n$, by the universal function theorem, so it is r.e. Suppose it were computable. Let $C = \{h \mid h(n) \text{ is defined}\}$. Then $c \mapsto \mathrm{eval}\ c \in C$ is the given predicate, so it is computable. The constant function $0$ is partial recursive and lies in $C$. The empty function is partial recursive. Rice's theorem gives that the empty function lies in $C$, which is false. If the negation were r.e., Post's theorem would make the predicate computable, which it is not. $\square$

**Proposition (Reductions form a preorder).** Many-one reducibility is reflexive and transitive, and each one-one reduction is a many-one reduction. The join $p \oplus q$ is the least upper bound: $p \oplus q \leq_0 r$ if and only if $p \leq_0 r$ and $q \leq_0 r$. Thus the many-one degrees form a join semilattice.

*Proof.* The identity is a reduction of $p$ to $p$. If $f$ reduces $p$ to $q$ and $g$ reduces $q$ to $r$, then $g \circ f$ is computable and $p\,a \iff q(f a) \iff r(g(f a))$. The maps $\mathrm{inl}$ and $\mathrm{inr}$ are injective and computable, and they reduce $p$ and $q$ to $p \oplus q$. So $p \oplus q \leq_0 r$ implies $p \leq_0 r$ and $q \leq_0 r$ by transitivity. Conversely, if $f$ reduces $p$ to $r$ and $g$ reduces $q$ to $r$, the function defined by cases, $\mathrm{inl}\ a \mapsto f(a)$ and $\mathrm{inr}\ b \mapsto g(b)$, is computable and reduces $p \oplus q$ to $r$. On degrees, reflexivity and transitivity give a partial order, and the join property says that $[p] + [q]$ is the supremum. $\square$

**Proposition (Oracles).** Let $O$ and $O'$ be sets of partial functions.

1. Each partial recursive function is recursive in $O$.
2. If $O \subseteq O'$, each function recursive in $O$ is recursive in $O'$.
3. If each $g \in O$ is recursive in $O'$, each function recursive in $O$ is recursive in $O'$.
4. If each $g \in O$ is partial recursive, each function recursive in $O$ is partial recursive. In particular, the functions recursive in $\emptyset$ are the partial recursive functions.
5. A function is partial recursive if and only if it is recursive in $\{g\}$ for every $g$.

*Proof.* Items 1 to 4 are inductions on the derivation. In item 3 the oracle case uses the hypothesis, and in item 4 the oracle case uses the hypothesis and the other cases repeat the constructors of $\mathrm{Partrec}$. For item 5, one direction is item 1. For the other, take $g$ the empty function, which is partial recursive, and apply item 4. $\square$

**Corollary (Turing reducibility).** Turing reducibility is reflexive and transitive, and Turing equivalence is an equivalence relation. The Turing degrees form a partial order. Its least element is the degree of the partial recursive functions.

*Proof.* Reflexivity: $g$ is recursive in $\{g\}$ by the oracle constructor. Transitivity: if $f \leq_T g$ and $g \leq_T h$, then item 3 with $O = \{g\}$ and $O' = \{h\}$ gives $f \leq_T h$. A preorder gives a partial order on its classes of equivalent elements, the antisymmetrization. By item 1, each partial recursive $f$ satisfies $f \leq_T g$ for every $g$, so the degree of partial recursive functions is the least element. Two partial recursive functions are Turing equivalent by the same item, so they form one degree. $\square$

### Examples

**Example (A one-one reduction between halting problems).** Let $H_n = \{c \mid \mathrm{eval}\ c\ n \text{ is defined}\}$. The map $c \mapsto \mathrm{comp}(c, \mathrm{zero})$ satisfies $\mathrm{eval}(\mathrm{comp}(c, \mathrm{zero}))\ m = \mathrm{eval}\ c\ 0$ for all $m$. Thus $c \in H_0 \iff \mathrm{comp}(c, \mathrm{zero}) \in H_5$. The map is computable and injective, because constructors of an inductive type are injective. So $H_0 \leq_1 H_5$. The same argument with $\mathrm{const}\ n$ in place of $\mathrm{zero}$ shows that all the sets $H_n$ are many-one equivalent.

**Example (Rice in practice).** Each of the following sets of codes is extensional, nonempty and not the full set, so it is not computable: the codes of total functions; the codes of the identity; the codes $c$ with $\mathrm{eval}\ c\ 0 = 3$; the codes of functions with finite domain. The set of codes with an even number is computable. It is not extensional: the code $\mathrm{zero}$, with number $0$, and the code $\mathrm{prec}(\mathrm{zero}, \mathrm{zero})$, with number $4 \cdot \mathrm{pair}(0, 0) + 5 = 5$, both compute the constant function $0$.

**Example (Post's theorem on finite sets).** Each finite set $S \subseteq \mathbb{N}$ is computable, since $n \in S$ is a finite disjunction of equalities. The set $\{n \mid n \text{ is even}\}$ is r.e. and has an r.e. complement, with the semi-decision procedures "search for $m$ with $2m = n$" and "search for $m$ with $2m + 1 = n$". The merge of the two procedures stops on each $n$ and decides parity.

**Example (A degree above the bottom).** Let $\chi$ be the characteristic function of $H_0$, a total function $\mathbb{N} \to \mathbb{N}$ through the numbering of codes. If $\chi$ were partial recursive, it would be computable, and $H_0$ would be computable. So the degree of $\chi$ is not the least degree. Each partial recursive function lies below it, so the degree of $\chi$ is strictly above the bottom.

### The library around it

::: mathlib
`ComputablePred.computable_iff_re_compl_re` · `Mathlib.Computability.RE`

`ComputablePred p` is `∃ _ : DecidablePred p, Computable fun a => decide (p a)`, with `ComputablePred.computable_iff` for the form with a `Bool` function. `REPred p` is `Partrec fun a => Part.assert (p a) fun _ => Part.some ()`. `ComputablePred.to_re`, `ComputablePred.not` and `Partrec.dom_re` are the closure facts, and `Partrec.merge` and `Partrec.merge'` are the merge lemma. `ComputablePred.computable_iff_re_compl_re` is Post's theorem with `[DecidablePred p]`, and `ComputablePred.computable_iff_re_compl_re'` is the classical form.

<?decl ComputablePred.computable_iff_re_compl_re?>
:::

::: mathlib
`ComputablePred.rice` · `Mathlib.Computability.Halting`

`ComputablePred.rice` is the theorem for sets of partial functions, and `ComputablePred.rice₂` is the form for extensional sets of codes. `ComputablePred.halting_problem n` states `¬ComputablePred fun c => (eval c n).Dom`, with the proof of the text, `ComputablePred.halting_problem_re` gives the r.e. half, and `ComputablePred.halting_problem_not_re` the complement.

<?decl ComputablePred.rice?>
:::

::: mathlib
`ManyOneDegree` · `Mathlib.Computability.Reduce`

`ManyOneReducible p q`, with notation `p ≤₀ q`, and `OneOneReducible p q`, with notation `p ≤₁ q`, are the reductions. `manyOneReducible_refl`, `ManyOneReducible.trans` and `OneOneReducible.to_many_one` are the preorder facts, and `ComputablePred.computable_of_manyOneReducible` transfers decidability. `ManyOneEquiv` and `OneOneEquiv` are the equivalences. The file writes `⊕'` for `Sum.elim` locally, and `disjoin_le` is the join property. `ManyOneDegree` is the quotient of `Set ℕ`, with `ManyOneDegree.of`, `ManyOneDegree.add_le` and `ManyOneDegree.instSemilatticeSup`.

<?decl ManyOneDegree?>
:::

::: mathlib
`Nat.RecursiveIn` · `Mathlib.Computability.RecursiveIn`

`Nat.RecursiveIn O` has the constructors of `Nat.Partrec` and one more, `oracle`. `RecursiveIn O f` is the version on primcodable types. The items of the proposition are `Nat.Partrec.recursiveIn`, `RecursiveIn.mono`, `Nat.RecursiveIn.subst`, `RecursiveIn.partrec_of_oracle`, `recursiveIn_empty_iff` and `partrec_iff_forall_recursiveIn_singleton`.

<?decl Nat.RecursiveIn?>
:::

::: mathlib
`TuringDegree` · `Mathlib.Computability.TuringDegree`

`TuringReducible f g` is an abbreviation for `RecursiveIn {g} f`, with the scoped notation `f ≤ᵀ g` in the namespace `Computability`. `TuringEquivalent` is `AntisymmRel TuringReducible`, with notation `≡ᵀ`. The facts of the corollary are `TuringReducible.refl`, `TuringReducible.trans`, `TuringEquivalent.equivalence`, `Partrec.turingReducible` and `partrec_iff_forall_turingReducible`. `TuringDegree` is the antisymmetrization, ordered by `TuringDegree.instPartialOrder`. The index of this edition has no declaration for the Turing jump or for a join of Turing degrees.

<?decl TuringDegree?>
:::

Common errors of a learner: The first error is to state undecidability with `¬ Decidable p`; in Lean each proposition is decidable classically, and the right statement is `¬ComputablePred p`. The second error is to apply Rice's theorem to a set of codes that is not extensional, such as the codes with an even number. The third error is to expect `≤ᵀ` without `open Computability`; the notation is scoped. The fourth error is to use `Nat.RecursiveIn` on a type other than ℕ; the predicate on primcodable types is `RecursiveIn`, and `RecursiveIn.iff_nat` relates the two.

### Exercises

1. (A) Show that the predicate "$\mathrm{eval}\ c\ 0 = 0$" on codes is r.e. but not computable. Hint: for r.e., use the universal function and the test of equality; for the other half, use Rice's theorem.
2. (A) Prove that if $p \leq_0 q$ and $q$ is r.e., then $p$ is r.e. Hint: compose the semi-decision procedure of $q$ with the reduction.
3. (A) Show that the set of codes of total functions is not computable. Hint: it contains the code $\mathrm{zero}$ and it does not contain a code of the empty function.
4. (B) Show that each r.e. set $p \subseteq \mathbb{N}$ is many-one reducible to $H_0$. Hint: for $a$, build by the smn theorem a code that ignores its input and runs the semi-decision procedure of $p$ on $a$.
5. (B) Prove that the r.e. predicates are closed under conjunction and disjunction. Hint: for conjunction, run the two procedures in sequence; for disjunction, use the merge lemma.
6. (B) Show that a nonempty set $p \subseteq \mathbb{N}$ is r.e. if and only if it is the range of a computable total function. Hint: for a nonempty r.e. set with an element $a_0$, map $\mathrm{pair}(x, k)$ to $x$ if the bounded evaluation of the procedure on $x$ succeeds within $k$, and to $a_0$ otherwise.
7. (C) Show that $H_0 \oplus \overline{H_0}$ is not many-one reducible to $H_0$, and that it is not many-one reducible to $\overline{H_0}$. Hint: a set many-one reducible to an r.e. set is r.e., and $\overline{H_0}$ and $H_0$ are each many-one reducible to the join.

### Notes and history

Turing proved the undecidability of the halting problem in 1936, and Church proved the undecidability of a related problem for the lambda calculus in the same year. Post introduced many-one and one-one reducibility and studied the r.e. degrees in the 1940s. Rice proved his theorem in 1953. Turing defined oracle machines in 1939, and Kleene and Post began the theory of Turing degrees.

The Mathlib files are by these authors, read from their headers: `Mathlib.Computability.Halting` and `Mathlib.Computability.RE` by Mario Carneiro, `Mathlib.Computability.Reduce` by Minchao Wu and Mario Carneiro, and `Mathlib.Computability.RecursiveIn` and `Mathlib.Computability.TuringDegree` by Tanner Duve and Elan Roth.

### Reference

<?reference?>
