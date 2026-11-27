---
title: Uncountable sets, codes and denumerable types
kind: theory
modules:
  - Mathlib.Basic.Denumerable
explains:
  E3: [Denumerable, Uncountable]
  E2: [Denumerable.eqv, Denumerable.ofNat, Denumerable.ofNat_encode, Nat.Subtype.denumerable, Denumerable.ofEncodableOfInfinite, nonempty_denumerable, nonempty_equiv_of_countable, not_countable, Set.not_countable_univ]
  E1: auto
families: []
requires: [V03.C05]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V03/C08/Examples.lean
  - MathlibHandbook/V03/C08/Exercises.lean
  - MathlibHandbook/V03/C08/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Uncountable sets, codes and denumerable types

### Overview

Section 1 showed that many sets are countable. This section shows the other side. The theorem of Cantor says that no set maps onto the set of its subsets. Two consequences follow: the set of the infinite binary sequences is not countable, and the set of the real numbers is not countable. The second part of the section looks at the countably infinite sets. Each of them is in bijection with $\mathbb{N}$, and each infinite subset of $\mathbb{N}$ is enumerated by its elements in increasing order. So there is exactly one infinite countable size.

Mathlib has three levels for these notions. The class `Countable` of Section 1 is a proposition. The class `Encodable` holds a chosen code $\alpha \to \mathbb{N}$ with a decoding function. The class `Denumerable` holds a chosen bijection with $\mathbb{N}$. The data classes matter when a definition, not a proof, needs the code: a program that lists the elements of a type, or a construction that must be computable.

### Definitions

**Definition (Uncountable).** A type is *uncountable* if it is not countable, that is, if there is no injective map from it to $\mathbb{N}$.

::: mathlib
`Uncountable` · `Mathlib.Basic.Countable.Defs`

The class `Uncountable α` has the one field `not_countable : ¬Countable α`. It is a class, so instance search can find it, for example for `ℝ` and for `ℕ → Bool`. The lemma `not_countable` extracts the field, and `Set.not_countable_univ` gives the set form `¬ (Set.univ : Set α).Countable`.

<?decl Uncountable?>
:::

**Definition (Encodable type).** An *encoding* of a type $\alpha$ is a pair of maps $\operatorname{enc} : \alpha \to \mathbb{N}$ and $\operatorname{dec} : \mathbb{N} \to \alpha \cup \{\mathrm{none}\}$ with $\operatorname{dec}(\operatorname{enc}(a)) = a$ for each $a$.

The law $\operatorname{dec} \circ \operatorname{enc} = \mathrm{id}$ makes $\operatorname{enc}$ injective, so an encodable type is countable. The map $\operatorname{dec}$ may answer "none" for the numbers that are not codes. Conversely, each countable type has an encoding, but the proof picks one with the axiom of choice.

::: mathlib
`Encodable` · `Mathlib.Logic.Encodable.Basic`

The class `Encodable α` has the fields `encode : α → ℕ`, `decode : ℕ → Option α` and `encodek : ∀ a, decode (encode a) = some a`. It is data: two different encodings give two different terms. So two instances of `Encodable α` can disagree, and a theorem should not take `[Encodable α]` as a hypothesis when `[Countable α]` is enough. The noncomputable `Encodable.ofCountable` builds an encoding from a `Countable` instance. The file belongs to the volume on logic and computability.

<?decl Encodable?>
:::

**Definition (Denumerable type).** A type $\alpha$ is *denumerable* if it has an encoding in which each number is a code, that is, if $\operatorname{enc}$ is a bijection $\alpha \to \mathbb{N}$.

::: mathlib
`Denumerable` · `Mathlib.Basic.Denumerable`

The class `Denumerable α` extends `Encodable α` with the field `decode_inv : ∀ n, ∃ a ∈ decode n, encode a = n`: each number decodes to an element whose code is the number. The bijection is `Denumerable.eqv α : α ≃ ℕ`, and the inverse map is `Denumerable.ofNat α : ℕ → α`, with the law `Denumerable.ofNat_encode`. Instances exist for `ℕ`, `ℤ`, `ℚ`, `ℕ × ℕ` and the lists of a denumerable type.

<?decl Denumerable?>
:::

### Theorems and proofs

**Theorem (Cantor).** Let $X$ be a set. There is no surjective map $f : X \to \mathcal{P}(X)$.

*Proof.* Let $f : X \to \mathcal{P}(X)$ be any map. Define $D = \{x \in X : x \notin f(x)\}$, a subset of $X$. Assume that $D = f(a)$ for some $a \in X$. If $a \in D$, then by the definition of $D$, $a \notin f(a) = D$, a contradiction. If $a \notin D$, then $a \notin f(a)$, so $a$ satisfies the condition that defines $D$, and $a \in D$, a contradiction. Both cases are impossible, so $D$ is not in the range of $f$. $\square$

The set $D$ is the *diagonal set*. The element $x$ is put in $D$ exactly when $x$ is not in its own set $f(x)$. So $D$ differs from each $f(x)$ at the element $x$. The same idea gives the next theorem.

::: mathlib
`Function.cantor_surjective` · `Mathlib.Logic.Function.Basic`

The statement `∀ f : α → Set α, ¬ Surjective f`. The dual form is `Function.cantor_injective`: no map `Set α → α` is injective. These lemmas belong to the volume on the language of Mathlib.

<?decl Function.cantor_surjective?>
:::

**Theorem (Binary sequences).** The set $\{0, 1\}^{\mathbb{N}}$ of the infinite sequences of zeros and ones is uncountable.

*Proof.* The set is not empty, so by the theorem (Injection and surjection) of Section 1 it is enough to show that no map $g : \mathbb{N} \to \{0, 1\}^{\mathbb{N}}$ is surjective. Let $g$ be a map, and write $g(n) = (g(n)_0, g(n)_1, \ldots)$. Define the sequence $d$ by $d_n = 1 - g(n)_n$. For each $n$, the sequences $d$ and $g(n)$ differ at the place $n$, because $d_n \ne g(n)_n$. So $d \ne g(n)$ for each $n$, and $d$ is not in the range of $g$. $\square$

A binary sequence is the indicator function of a subset of $\mathbb{N}$, so this is the theorem of Cantor for $X = \mathbb{N}$, and the sequence $d$ is the indicator of the diagonal set. The proof has the form of a table: row $n$ is the sequence $g(n)$, and $d$ reverses the diagonal.

**Theorem (The real numbers).** The interval $[0, 1]$, and so the set $\mathbb{R}$, is uncountable.

*Proof.* The plan: from a sequence $x_0, x_1, \ldots$ in $[0, 1]$, build nested closed intervals that avoid $x_0$, then $x_1$, and so on, and take a point in all of them. Let $(x_n)_{n \ge 0}$ be any sequence of points of $[0, 1]$. It is enough to find $c \in [0, 1]$ with $c \ne x_n$ for each $n$.

Put $I_{-1} = [0, 1]$. Assume that $I_{n-1} = [a, b]$ with $a < b$ is built. Divide it into three closed thirds and keep the first and the last, $L = [a, a + \frac{b - a}{3}]$ and $R = [b - \frac{b - a}{3}, b]$. These two intervals are disjoint, so $x_n$ is not in at least one of them. Let $I_n$ be $L$ if $x_n \notin L$, and $R$ otherwise. Then $I_n \subseteq I_{n-1}$, $x_n \notin I_n$, and the length of $I_n$ is $3^{-(n+1)}$.

Write $I_n = [a_n, b_n]$. The sequence $(a_n)$ is increasing and bounded above by $1$, because the intervals are nested. Let $c = \sup_n a_n$, which exists by the completeness of $\mathbb{R}$. For each $m$ and each $n \ge m$, $a_n \le b_n \le b_m$, so $b_m$ is an upper bound of all $a_n$ with $n \ge m$, and so of all $a_n$. So $a_m \le c \le b_m$, that is, $c \in I_m$ for each $m$. Since $x_m \notin I_m$, $c \ne x_m$. So the sequence does not list $c$, and no sequence lists all of $[0, 1]$. A subset of a countable set is countable, so $\mathbb{R}$ is uncountable too. $\square$

The completeness is essential. The same construction in $\mathbb{Q} \cap [0, 1]$, which is countable, gives nested intervals whose endpoints converge to a number that may be irrational, and so may not be in $\mathbb{Q}$.

::: mathlib
`Cardinal.not_countable_real` · `Mathlib.Analysis.Real.Cardinality`

The statement `¬ (Set.univ : Set ℝ).Countable`. Mathlib proves more: `Cardinal.mk_real` says that $\mathbb{R}$ has the cardinal $2^{\aleph_0}$. The route is a map from the binary sequences into $\mathbb{R}$ by expansions in base three, which is injective because the digits avoid the ambiguity of $0.0222\ldots = 0.1$, and then the theorem of Cantor for cardinals, `Cardinal.cantor`. These declarations belong to the volumes on analysis and on set theory.

<?decl Cardinal.not_countable_real?>
:::

**Theorem (Infinite subsets of $\mathbb{N}$).** Let $S \subseteq \mathbb{N}$ be infinite. Then the map $e : \mathbb{N} \to S$ defined by $e(0) = \min S$ and $e(k + 1) = \min \{x \in S : x > e(k)\}$ is a bijection, and it is strictly increasing.

*Proof.* The definition makes sense: $S$ is not empty, and for each $k$ the set $\{x \in S : x > e(k)\}$ is not empty, because it is $S$ minus a finite set, and $S$ is infinite. By the definition, $e(k + 1) > e(k)$, so $e$ is strictly increasing, and in particular injective. By induction, $e(k) \ge k$: $e(0) \ge 0$, and $e(k + 1) > e(k) \ge k$ gives $e(k + 1) \ge k + 1$.

For surjectivity, let $x \in S$. Then $e(x) \ge x$, so the set of the $k$ with $e(k) \ge x$ is not empty. Let $k$ be its least element. If $k = 0$, then $e(0) = \min S \le x \le e(0)$, so $e(0) = x$. If $k \ge 1$, then $e(k - 1) < x$ by the minimality of $k$. So $x$ is an element of $S$ above $e(k - 1)$, and $e(k)$ is the least such element, so $e(k) \le x$. With $e(k) \ge x$ this gives $e(k) = x$. $\square$

::: mathlib
`Nat.Subtype.denumerable` · `Mathlib.Basic.Denumerable`

The instance `Denumerable s` for a set `s : Set ℕ` with a decidable membership and an instance `Infinite s`. Its bijection is the enumeration in increasing order of the theorem. A related function of the volume on numbers is `Nat.nth p n`, the $n$th natural number with the property $p$, counted from $0$.

<?decl Nat.Subtype.denumerable?>
:::

**Theorem (Countably infinite types).** Let $\alpha$ be countable and infinite. Then there is a bijection $\alpha \to \mathbb{N}$. So any two countably infinite types are in bijection.

*Proof.* Let $f : \alpha \to \mathbb{N}$ be injective, and let $S = f(\alpha)$. The map $f$ is a bijection from $\alpha$ onto $S$. The set $S$ is infinite: if it were finite, then $\alpha$, which is in bijection with it, would be finite. By the previous theorem there is a bijection $e : \mathbb{N} \to S$. Then $e^{-1} \circ f : \alpha \to \mathbb{N}$ is a bijection. For two countably infinite types $\alpha$ and $\beta$, compose the bijection $\alpha \to \mathbb{N}$ with the inverse of the bijection $\beta \to \mathbb{N}$. $\square$

::: mathlib
`nonempty_equiv_of_countable` · `Mathlib.Basic.Denumerable`

The second statement: `[Countable α] [Infinite α] [Countable β] [Infinite β] → Nonempty (α ≃ β)`. The result is `Nonempty` of an equivalence, a proposition, because the proof uses choice to pick the codes. The first statement is `nonempty_denumerable`, and the data form, from an encoding, is `Denumerable.ofEncodableOfInfinite`.

<?decl nonempty_equiv_of_countable?>
:::

::: mathlib
`Denumerable.eqv` · `Mathlib.Basic.Denumerable`

The equivalence `α ≃ ℕ` of a denumerable type. Use it to move a statement about `ℕ` to `α`, for example to list the elements of `α` as `(Denumerable.eqv α).symm 0`, `(Denumerable.eqv α).symm 1`, and so on.

<?decl Denumerable.eqv?>
:::

### Examples

**Example (Cantor).** The theorem of Cantor in the form of Mathlib, for a type `α` and a map `f : α → Set α`.

<?lean MathlibHandbook/V03/C08/Examples.lean#cantor?>

**Example (A diagonal set).** Let $f : \{1, 2, 3\} \to \mathcal{P}(\{1, 2, 3\})$ be given by $f(1) = \{1, 2\}$, $f(2) = \{3\}$, $f(3) = \{1, 3\}$. Then $1 \in f(1)$, $2 \notin f(2)$ and $3 \in f(3)$, so $D = \{2\}$. Indeed $\{2\}$ is not one of the three values. The set $\mathcal{P}(\{1, 2, 3\})$ has $8$ elements, so the theorem is no surprise here. The proof gives the same kind of witness for every set, finite or infinite.

**Example (A diagonal sequence).** Let $g(0) = 0000\ldots$, $g(1) = 1111\ldots$, $g(2) = 0101\ldots$, $g(3) = 1010\ldots$, and $g(n) = 0000\ldots$ for $n \ge 4$. The diagonal digits are $g(0)_0 = 0$, $g(1)_1 = 1$, $g(2)_2 = 0$, $g(3)_3 = 0$, and $0$ after that. So $d = 1011\,1111\ldots$. It differs from $g(0)$ at place $0$, from $g(1)$ at place $1$, from $g(2)$ at place $2$, from $g(3)$ at place $3$, and from each later $g(n)$ at place $n$.

**Example (The real numbers).** The set of the real numbers is not countable.

<?lean MathlibHandbook/V03/C08/Examples.lean#real?>

**Example (Nested thirds).** Take $x_0 = 0$, $x_1 = 1$, $x_2 = \frac{1}{2}$. Then $I_{-1} = [0, 1]$, and $x_0 = 0 \in [0, \frac13]$, so $I_0 = [\frac23, 1]$. Next $x_1 = 1 \in [\frac89, 1]$, so $I_1 = [\frac23, \frac79]$. Next $x_2 = \frac12$ is not in $[\frac23, \frac{19}{27}]$, so $I_2 = [\frac23, \frac{19}{27}]$. Each later point of the sequence removes another third, and the point $c$ that remains differs from all $x_n$.

**Example (An enumeration).** The set $S$ of the primes is infinite. The enumeration of the theorem (Infinite subsets of $\mathbb{N}$) is $e(0) = 2$, $e(1) = 3$, $e(2) = 5$, $e(3) = 7$, $e(4) = 11$. The set of the even numbers gives $e(k) = 2k$, and the set of the squares gives $e(k) = k^2$.

**Example (Irrational numbers).** The set $\mathbb{R} \setminus \mathbb{Q}$ is uncountable. If it were countable, then $\mathbb{R} = \mathbb{Q} \cup (\mathbb{R} \setminus \mathbb{Q})$ would be a union of two countable sets, and so countable. The same argument with the countable set of the algebraic numbers shows that the transcendental numbers form an uncountable set. In particular they exist.

**Counterexample (A finite subset).** The theorem (Infinite subsets of $\mathbb{N}$) needs $S$ to be infinite. For $S = \{3, 8\}$, the definition gives $e(0) = 3$, $e(1) = 8$, and $e(2)$ is the least element of an empty set, which does not exist. A finite set has no bijection with $\mathbb{N}$.

### Common errors

1. A learner proves "uncountable" by showing that a set is infinite. Infinite sets can be countable, like $\mathbb{N}$ and $\mathbb{Q}$. An uncountability proof needs a diagonal argument or an injection of a known uncountable set.
2. A learner writes the diagonal sequence as $d_n = g(n)_n$, with no change. The change at each place is the point of the proof.
3. A learner takes `[Encodable α]` as a hypothesis of a theorem. Two instances can then disagree, and the user of the theorem may have no instance at hand. Take `[Countable α]` and build an encoding in the proof with `Encodable.ofCountable` if one is needed.
4. A learner applies the nested intervals argument to open intervals. Nested open intervals can have an empty intersection: $\bigcap_n (0, \frac1n) = \emptyset$. The proof needs closed intervals.

### The library around it

The file `Mathlib.Basic.Denumerable` has the class `Denumerable`, its equivalence `Denumerable.eqv` and inverse `Denumerable.ofNat` with the laws `Denumerable.ofNat_encode` and `Denumerable.encode_ofNat`, the instances for `ℕ`, products, sums, sigma types, options and lists, and the bridges `Denumerable.ofEncodableOfInfinite`, `nonempty_denumerable` and `nonempty_equiv_of_countable`. It also has the enumeration `Nat.Subtype.ofNat` of an infinite set of natural numbers, with the instance `Nat.Subtype.denumerable`. The class `Uncountable` and the lemma `not_countable` are in `Mathlib.Basic.Countable.Defs`, and `Set.not_countable_univ` is in `Mathlib.Data.Set.Countable`. The class `Encodable` and its constructions (`Encodable.ofLeftInverse`, `Encodable.ofEquiv`, `Encodable.ofCountable`) are in `Mathlib.Logic.Encodable.Basic`, and the cardinals that measure the uncountable sizes are in the volume on set theory. The table at the end lists the declarations of this section.

### Exercises

1. (A) For $f : \{1, 2, 3, 4\} \to \mathcal{P}(\{1, 2, 3, 4\})$ with $f(1) = \emptyset$, $f(2) = \{1, 2\}$, $f(3) = \{1, 2, 4\}$, $f(4) = \{4\}$, compute the diagonal set $D$.
2. (A) Explain why the set of the finite binary sequences is countable and the set of the infinite binary sequences is not.
3. (A) Give the first five values of the enumeration of $\{n \in \mathbb{N} : n \equiv 2 \pmod 3\}$, and a formula for $e(k)$.
4. (B) Prove that the set $\mathbb{N}^{\mathbb{N}}$ of all sequences of natural numbers is uncountable, by a diagonal argument.
5. (B) Prove that each nonempty open interval $(a, b)$ of $\mathbb{R}$ is uncountable. Hint: the map $t \mapsto a + t(b - a)$.
6. (B) Prove that a countable set $S \subseteq \mathbb{R}$ has a countable complement only if $\mathbb{R}$ is countable, and conclude that the complement of a countable set of real numbers is uncountable.
7. (B) Prove that the set of the infinite subsets of $\mathbb{N}$ is uncountable. Hint: the finite subsets form a countable set.
8. (C) Prove that each infinite set $X$ has a countably infinite subset. Hint: choose $x_0 \in X$, then $x_1 \in X \setminus \{x_0\}$, and so on; say where the proof uses a choice.
9. (C) Prove that for each infinite set $X$ and countable set $C$, the sets $X$ and $X \cup C$ have the same size. Hint: take a countably infinite $A \subseteq X$ by the previous exercise, and build a bijection $A \to A \cup (C \setminus X)$.

### Notes and history

Cantor proved in 1874 that the real numbers are uncountable, with an argument of nested intervals close to the one of this section. He found the diagonal argument in 1891, in the paper *Über eine elementare Frage der Mannigfaltigkeitslehre*, and the theorem on the power set follows the same idea. The existence of transcendental numbers, shown by Liouville in 1844 with explicit examples, followed from the work of 1874 with no example. The fact that each infinite set has a countably infinite subset needs a weak form of choice, the axiom of dependent choice. Halmos, *Naive Set Theory*, gives the theory of the countable sets in its sections on cardinal numbers.

In Mathlib, `Encodable` and `Denumerable` were written by Leonardo de Moura and Mario Carneiro for the Lean 3 library, in the work on computability, where a code of each type is part of the data. The class `Countable` came later as the proposition form. The file `Mathlib.Basic.Denumerable` has the authors line of Mario Carneiro (2018). MIL shows the diagonal argument in its chapter on sets and functions.

### Reference

<?reference?>
