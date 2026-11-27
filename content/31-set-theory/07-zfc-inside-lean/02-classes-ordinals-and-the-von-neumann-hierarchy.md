---
title: Classes, ordinals and the von Neumann hierarchy
kind: theory
modules:
  - Mathlib.SetTheory.ZFC.Class
  - Mathlib.SetTheory.ZFC.Ordinal
  - Mathlib.SetTheory.ZFC.Rank
  - Mathlib.SetTheory.ZFC.VonNeumann
  - Mathlib.SetTheory.ZFC.Cardinal
explains:
  E3: [ZFClass, ZFSet.IsOrdinal, ZFSet.rank, ZFSet.vonNeumann, ZFSet.card]
  E2: [ZFClass.CMem, ZFClass.univ_notCMem_univ, ZFClass.iota, ZFClass.fval, ZFSet.choice, ZFSet.choice_isFunc, ZFSet.choice_cmem, ZFSet.coeEquiv, ZFSet.IsTransitive, ZFSet.IsOrdinal.mem, ZFSet.IsOrdinal.mem_trichotomous, ZFSet.isOrdinal_iff_isWellOrder, Ordinal.toZFSet, Ordinal.toZFSetIso, ZFSet.isOrdinal_notCMem_univ, ZFSet.rank_lt_of_mem, ZFSet.rank_powerset, ZFSet.mem_vonNeumann, ZFSet.vonNeumann_add_one, ZFSet.iUnion_vonNeumann, ZFSet.card_vonNeumann, ZFSet.card_powerset]
  E1: auto
families: [ZFSet.rank_*, ZFSet.vonNeumann_*, ZFSet.IsOrdinal.*, ZFSet.IsTransitive.*, Ordinal.toZFSet_*, ZFSet.card_*]
requires: [V01.C01, V01.C03, V04.C01, V31.C02, V31.C03, V31.C05, V31.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Classes, ordinals and the von Neumann hierarchy

### Overview

Section 1 built the type `ZFSet` and checked the axioms of ZFC except choice. This section adds the next layer of a first course in axiomatic set theory. A *class* is an arbitrary collection of ZFC sets; some classes, such as the class of all sets, are too large to be sets. A *von Neumann ordinal* is a transitive set that is well-ordered by membership. The ordinals of Chapter 2 are defined as isomorphism classes of well-orders, and this section proves that they correspond exactly to the von Neumann ordinals. The *rank* of a set measures how deep its membership tree is, and the *von Neumann hierarchy* $V_\alpha$ collects the sets of rank below $\alpha$. Every ZFC set lies in some $V_\alpha$, and the cardinality of $V_\alpha$ is a beth number of Chapter 5. The section ends with the axiom of choice and the cardinality of a ZFC set.

### Definitions

**Definition (Class).** A *class* is a set of ZFC sets in the sense of Lean, that is, a term of `Set ZFSet`. Each ZFC set $x$ gives the class of its elements. A class $A$ is a *member* of a class $B$, written $A \mathrel{{}^c{\in}} B$, if $A$ is the class of some ZFC set $x$ and $x \in B$. The class $\mathrm{univ}$ contains all ZFC sets.

A class is a predicate on sets with no bound on its size. The membership relation on classes says that only a class that comes from a set can be a member. This matches the usage of von Neumann-Bernays-Gödel set theory, where a *proper class* is a class that is not a member of any class.

::: mathlib
`ZFClass` · `Mathlib.SetTheory.ZFC.Class`

`ZFClass.{u}` is an abbreviation for `Set ZFSet.{u}`, so every lemma about sets in the sense of Lean applies. The coercion from `ZFSet` to `ZFClass` is the `SetLike` coercion of Section 1. Membership of classes is `ZFClass.CMem` with the scoped notation `A ᶜ∈ B`. An older API under the name `Class` is deprecated in this edition (since 2026-09-25); use `ZFClass`.

<?decl ZFClass?>
:::

**Definition (Transitive set, ordinal).** A ZFC set $x$ is *transitive* if each element of $x$ is a subset of $x$: $z \in y \in x$ implies $z \in x$. A set $x$ is a *von Neumann ordinal* if $x$ is transitive and membership is transitive on the elements of $x$: for $y, z, w$ with $y \in z \in w \in x$, also $y \in w$.

By $\in$-induction, membership is well-founded on any set. So an ordinal in this sense is a transitive set on which $\in$ is a strict well-order, as the theorem below proves.

::: mathlib
`ZFSet.IsOrdinal` · `Mathlib.SetTheory.ZFC.Ordinal`

`IsOrdinal x` is a structure with two fields, `isTransitive : x.IsTransitive` and `mem_trans'`, the second condition of the definition. The predicate `ZFSet.IsTransitive x` is `∀ y ∈ x, y ⊆ x`. The equivalent forms `ZFSet.isOrdinal_iff_isWellOrder` and `ZFSet.isOrdinal_iff_forall_mem_isTransitive` are proved in the same file.

<?decl ZFSet.IsOrdinal?>
:::

**Definition (Rank).** The *rank* of a ZFC set is defined by $\in$-recursion:
$$\mathrm{rank}(x) = \sup_{y \in x} (\mathrm{rank}(y) + 1).$$
The empty set has rank $0$, and the rank of $x$ is the least ordinal strictly above the ranks of all elements of $x$.

::: mathlib
`ZFSet.rank` · `Mathlib.SetTheory.ZFC.Rank`

`ZFSet.rank : ZFSet.{u} → Ordinal.{u}` is defined from `PSet.rank ⟨_, A⟩ = ⨆ a, succ (rank (A a))`, a supremum over the index type, and `PSet.rank_congr` shows that it respects equivalence. The lemma `ZFSet.rank_eq_wfRank` identifies it with the general rank `WellFounded.rank` of Chapter 2 for the relation `∈`, up to a universe lift.

<?decl ZFSet.rank?>
:::

**Definition (Von Neumann hierarchy).** For an ordinal $\alpha$, by recursion on $\alpha$,
$$V_\alpha = \bigcup_{\beta < \alpha} \mathcal{P}(V_\beta).$$
So $V_0 = \emptyset$, $V_{\beta + 1} = \mathcal{P}(V_\beta)$, and $V_\lambda = \bigcup_{\beta < \lambda} V_\beta$ for a limit ordinal $\lambda$.

::: mathlib
`ZFSet.vonNeumann` · `Mathlib.SetTheory.ZFC.VonNeumann`

`ZFSet.vonNeumann (o : Ordinal.{u}) : ZFSet.{u}` has the scoped notation `V_ o`. The three cases are `ZFSet.vonNeumann_zero`, `ZFSet.vonNeumann_add_one` and `ZFSet.vonNeumann_of_isSuccPrelimit`. The name `ZFSet.vonNeumann_succ` is deprecated in favour of `vonNeumann_add_one`.

<?decl ZFSet.vonNeumann?>
:::

**Definition (Cardinality of a ZFC set).** The *cardinality* of a ZFC set $x$ of level $u$ is the cardinal of the type of its elements, brought down to universe $u$.

::: mathlib
`ZFSet.card` · `Mathlib.SetTheory.ZFC.Cardinal`

`ZFSet.card x = #(Shrink x)`. The type of elements of `x : ZFSet.{u}` lives in `Type (u + 1)`, but it is small (`ZFSet.small_coe` of Section 1), so `Shrink` gives an equivalent type in `Type u`. The lemma `ZFSet.cardinalMk_coe_sort` relates `#x` to the lift of `card x`.

<?decl ZFSet.card?>
:::

### Theorems and proofs

**Theorem (Russell).** There is no set of all sets: $\mathrm{univ} \mathrel{{}^c{\notin}} \mathrm{univ}$.

*Proof.* The relation ${}^c{\in}$ on classes is well-founded, because $A \mathrel{{}^c{\in}} B$ requires $A$ to be a set, and $\in$ is well-founded on sets. A well-founded relation is irreflexive. So no class is a member of itself, and in particular $\mathrm{univ} \mathrel{{}^c{\notin}} \mathrm{univ}$. $\square$

Exercise 5 of Section 1 gives the classical proof with separation. In Mathlib the theorem is `ZFClass.univ_notCMem_univ`.

**Theorem (Elements and trichotomy).** Let $x$ be an ordinal. Then each $y \in x$ is an ordinal. For two ordinals $x$ and $y$, exactly one of $x \in y$, $x = y$, $y \in x$ holds. Consequently $\in$ is a strict well-order on each ordinal.

*Proof.* Let $y \in x$. If $w \in v \in y$, then $v \in x$ and $w \in x$ by transitivity of $x$, and $w \in v \in y \in x$ gives $w \in y$ by the second condition on $x$. So $y$ is transitive. The second condition for $y$ follows from that for $x$, since the elements of $y$ are elements of $x$.

For trichotomy, use induction on $x$ and on $y$: assume that the statement holds for each pair $(z, y)$ with $z \in x$ and for each pair $(x, w)$ with $w \in y$. Suppose that $x \notin y$ and $y \notin x$. Let $z \in x$. By the induction hypothesis, $z \in y$, $z = y$ or $y \in z$. If $z = y$, then $y \in x$. If $y \in z$, then $y \in x$ by transitivity of $x$. Both are excluded, so $z \in y$, and $x \subseteq y$. The same argument with the roles exchanged gives $y \subseteq x$, so $x = y$. At most one of the three cases holds, since $x \in y$ and $y \in x$ give $x \in x$ by transitivity, and $x \in x$ contradicts well-foundedness. $\square$

**Theorem (Von Neumann ordinals).** For an ordinal $o$ in the sense of Chapter 2, put
$$\overline{o} = \{\overline{a} \mid a < o\},$$
by well-founded recursion on $o$. Then $\overline{o}$ is a von Neumann ordinal, $\mathrm{rank}(\overline{o}) = o$, and $o \mapsto \overline{o}$ is an order isomorphism from the ordinals onto the von Neumann ordinals, ordered by $\in$, with inverse $\mathrm{rank}$.

*Proof.* By induction on $o$. The elements of $\overline{o}$ are the $\overline{a}$ for $a < o$. If $\overline{b} \in \overline{a}$ with $a < o$, then $b < a < o$, so $\overline{b} \in \overline{o}$; this proves transitivity, and the second condition is the transitivity of $<$. The rank of $\overline{o}$ is $\sup_{a < o} (a + 1) = o$, by the induction hypothesis $\mathrm{rank}(\overline{a}) = a$. So $\overline{a} \in \overline{b}$ if and only if $a < b$, and the map is injective because the rank recovers $o$.

For surjectivity, let $x$ be a von Neumann ordinal, and prove $\overline{\mathrm{rank}(x)} = x$ by $\in$-induction. The elements of $x$ are ordinals, so by induction $x = \{\overline{\mathrm{rank}(y)} \mid y \in x\}$. Let $S$ be the set of the ranks of the elements of $x$. If $a < \mathrm{rank}(y)$ for some $y \in x$, then $\overline{a} \in \overline{\mathrm{rank}(y)} = y$, so $\overline{a} \in x$ by transitivity, and $a = \mathrm{rank}(\overline{a}) \in S$. So $S$ is downward closed. A downward closed set of ordinals is the set of ordinals below $\sup_{s \in S}(s + 1)$, and this supremum is $\mathrm{rank}(x)$. So $x = \{\overline{a} \mid a < \mathrm{rank}(x)\} = \overline{\mathrm{rank}(x)}$. $\square$

::: mathlib
`Ordinal.toZFSetIso` · `Mathlib.SetTheory.ZFC.Ordinal`

`Ordinal.toZFSet : Ordinal.{u} → ZFSet.{u}` is the map $o \mapsto \overline{o}$, and `Ordinal.toZFSetIso : Ordinal ≃o {x // ZFSet.IsOrdinal x}` is the isomorphism. On the set side the order is `⊆`, which agrees with $\in$ or equality on ordinals. Useful lemmas are `Ordinal.toZFSet_mem_toZFSet_iff`, `ZFSet.rank_toZFSet`, `ZFSet.IsOrdinal.toZFSet_rank_eq`, `Ordinal.toZFSet_zero` and `Ordinal.toZFSet_add_one`.

<?decl Ordinal.toZFSetIso?>
:::

**Theorem (Burali-Forti).** The von Neumann ordinals form a proper class: the class $\{x \mid x \text{ is an ordinal}\}$ is not a set.

*Proof.* Assume that a ZFC set $x$ has exactly the ordinals as elements. Each element of an ordinal is an ordinal, so each element of $x$ is a subset of $x$, and $x$ is transitive. If $y \in z \in w \in x$, then $w$ is an ordinal and $y \in w$ by its transitivity. So $x$ is an ordinal, hence $x \in x$, which contradicts well-foundedness. $\square$

The Burali-Forti argument for the ordinals of Chapter 2 is about universes: the type `Ordinal.{u}` lives in `Type (u + 1)`, and its order type is the ordinal `Ordinal.univ.{u, u+1}` of the next universe. The theorem here is the form of the argument inside one universe of sets.

**Theorem (Rank and the hierarchy).** For a ZFC set $x$ and an ordinal $\alpha$:

1. if $y \in x$ then $\mathrm{rank}(y) < \mathrm{rank}(x)$;
2. $\mathrm{rank}(\mathcal{P}(x)) = \mathrm{rank}(x) + 1$;
3. $x \subseteq V_\alpha$ if and only if $\mathrm{rank}(x) \le \alpha$, and $x \in V_\alpha$ if and only if $\mathrm{rank}(x) < \alpha$;
4. each set is an element of some $V_\alpha$, namely $V_{\mathrm{rank}(x) + 1}$.

*Proof.* Part 1 is the definition: $\mathrm{rank}(x)$ is at least $\mathrm{rank}(y) + 1$.

Part 2. Each $z \in \mathcal{P}(x)$ is a subset of $x$. The rank is monotone for $\subseteq$, since the supremum over a smaller set is smaller. So $\mathrm{rank}(z) \le \mathrm{rank}(x)$ and $\mathrm{rank}(\mathcal{P}(x)) \le \mathrm{rank}(x) + 1$. Since $x \in \mathcal{P}(x)$, part 1 gives the converse inequality.

Part 3, by induction on $\alpha$, for all $x$ at once. Suppose $x \subseteq V_\alpha$ and let $y \in x$. By the definition of $V_\alpha$, $y \subseteq V_\beta$ for some $\beta < \alpha$, so $\mathrm{rank}(y) \le \beta$ by induction and $\mathrm{rank}(y) + 1 \le \alpha$. Taking the supremum, $\mathrm{rank}(x) \le \alpha$. Conversely, suppose $\mathrm{rank}(x) \le \alpha$ and let $y \in x$. Put $\beta = \mathrm{rank}(y) < \alpha$. By induction $y \subseteq V_\beta$, so $y \in \mathcal{P}(V_\beta) \subseteq V_\alpha$. The statement for $\in$ follows: $x \in V_\alpha$ means $x \subseteq V_\beta$ for some $\beta < \alpha$, that is, $\mathrm{rank}(x) \le \beta < \alpha$.

Part 4 follows from part 3 with $\alpha = \mathrm{rank}(x) + 1$. $\square$

::: mathlib
`ZFSet.mem_vonNeumann` · `Mathlib.SetTheory.ZFC.VonNeumann`

`ZFSet.mem_vonNeumann : x ∈ V_ o ↔ rank x < o` and `ZFSet.subset_vonNeumann : x ⊆ V_ o ↔ rank x ≤ o` are parts 3. Part 4 is stated in two ways: `ZFSet.exists_mem_vonNeumann` and `ZFSet.iUnion_vonNeumann : ⋃ o, (V_ o : ZFClass) = .univ`. Each `V_ o` is transitive (`ZFSet.isTransitive_vonNeumann`) and has rank `o` (`ZFSet.rank_vonNeumann`).

<?decl ZFSet.mem_vonNeumann?>
:::

**Theorem (Size of the hierarchy).** For each ordinal $\alpha$, $|V_\alpha| = \beth'_\alpha$, where the pre-beth numbers of Chapter 5 satisfy $\beth'_0 = 0$, $\beth'_{\alpha+1} = 2^{\beth'_\alpha}$ and $\beth'_\lambda = \sup_{\alpha < \lambda} \beth'_\alpha$ at limits. In particular $|V_\omega| = \aleph_0$ and $|V_{\omega + \alpha}| = \beth_\alpha$.

*Proof.* By induction on $\alpha$. The case $0$ is $V_0 = \emptyset$. At a successor, $|\mathcal{P}(x)| = 2^{|x|}$ (`ZFSet.card_powerset`, which uses the equivalence between subsets of a set and subsets of its type of elements), so $|V_{\alpha+1}| = 2^{\beth'_\alpha} = \beth'_{\alpha+1}$. At a limit $\lambda$, the union $V_\lambda$ of the increasing chain $V_\alpha$ has cardinality at least each $|V_\alpha|$, so $|V_\lambda| \ge \beth'_\lambda$. For the upper bound, $|V_\lambda| \le \sum_{\alpha < \lambda} |V_\alpha| \le |\lambda| \cdot \beth'_\lambda$, and $|\lambda| \le \beth'_\lambda$ because $\beth'$ is strictly increasing (`Ordinal.card_le_card_vonNeumann` records $|\lambda| \le |V_\lambda|$). The product of two infinite cardinals is their maximum, by Chapter 5. The last claims are $\beth'_\omega = \aleph_0$ and $\beth_\alpha = \beth'_{\omega + \alpha}$, the definition of `Cardinal.beth`. $\square$

**Theorem (Choice).** Let $x$ be a ZFC set with $\emptyset \notin x$. There is a set $c$ that is a function from $x$ to $\bigcup x$ with $c(y) \in y$ for each $y \in x$.

*Proof.* For each nonempty $y$ choose an element $\varepsilon(y) \in y$ with Hilbert's choice operator, which Lean provides from the axiom of choice of its type theory. By the axiom of replacement of Section 1, in its form for arbitrary functions, the set $c = \{(y, \varepsilon(y)) \mid y \in x\}$ exists. It is a subset of $x \times \bigcup x$ with exactly one pair for each $y \in x$, by injectivity of pairs. $\square$

::: mathlib
`ZFSet.choice` · `Mathlib.SetTheory.ZFC.Class`

`ZFSet.choice x` is the set $c$ of the proof. `ZFSet.choice_isFunc` says `IsFunc x (⋃₀ x) (choice x)` under `∅ ∉ x`, and `ZFSet.choice_cmem` says `choice x ′ y ᶜ∈ y` for `y ∈ x`. Here `F ′ A` is `ZFClass.fval`, the value of a class function, defined with the definite description `ZFClass.iota`. So the choice axiom of ZFC holds in `ZFSet` because Lean has `Classical.choice`.

<?decl ZFSet.choice_isFunc?>
:::

### Examples

**Example (The first levels).** By the theorem on rank, $V_n$ is the set of sets of rank below $n$:

- $V_0 = \emptyset$, $V_1 = \{\emptyset\}$, $V_2 = \{\emptyset, \{\emptyset\}\}$.
- $V_3 = \mathcal{P}(V_2) = \{\emptyset, \{\emptyset\}, \{\{\emptyset\}\}, \{\emptyset, \{\emptyset\}\}\}$.
- $|V_4| = 2^4 = 16$ and $|V_5| = 2^{16} = 65536$.

The pre-beth numbers $\beth'_n$ are $0, 1, 2, 4, 16, 65536, \dots$, the same sequence, as the size theorem says. The set $V_\omega$ of hereditarily finite sets is countable, and $V_{\omega+1} = \mathcal{P}(V_\omega)$ has the cardinality $2^{\aleph_0}$ of the continuum.

**Counterexample (A transitive set that is not an ordinal).** Let $x = \{\emptyset, \{\emptyset\}, \{\{\emptyset\}\}\}$. Each element of $x$ is a subset of $x$: $\emptyset$ trivially, $\{\emptyset\}$ since $\emptyset \in x$, and $\{\{\emptyset\}\}$ since $\{\emptyset\} \in x$. So $x$ is transitive. But $\emptyset \in \{\emptyset\} \in \{\{\emptyset\}\}$ and $\emptyset \notin \{\{\emptyset\}\}$, so membership is not transitive on $x$, and $x$ is not an ordinal. The two conditions in `ZFSet.IsOrdinal` are independent. The set $\{\{\emptyset\}\}$ is an ordinal of neither kind: it is not transitive, since $\emptyset \notin \{\{\emptyset\}\}$, yet membership on it is trivially transitive.

**Example (Rank of a pair).** For ZFC sets $x$ and $y$, the lemmas `ZFSet.rank_singleton` and `ZFSet.rank_pair` give $\mathrm{rank}\{x\} = \mathrm{rank}(x) + 1$ and $\mathrm{rank}\{x, y\} = \max(\mathrm{rank}(x), \mathrm{rank}(y)) + 1$. So the Kuratowski pair has $\mathrm{rank}\,(x, y) = \max(\mathrm{rank}(x), \mathrm{rank}(y)) + 2$. For natural numbers, $\mathrm{rank}(\overline{n}) = n$, and $(\overline{1}, \overline{3})$ has rank $5$.

**Example (Ordinals as sets).** The map of the isomorphism theorem sends $0$ to $\emptyset$ and $o + 1$ to $\overline{o} \cup \{\overline{o}\}$, by `Ordinal.toZFSet_add_one`. So on the natural numbers it agrees with the pre-sets $[n]$ of Section 1, and $\overline{\omega}$ is the set $\{[0], [1], [2], \dots\}$. Since $\mathrm{rank}(\overline{o}) = o$, the set $\overline{o}$ is in $V_{o+1}$ and is a subset of $V_o$ (`Ordinal.toZFSet_subset_vonNeumann`).

### The library around it

The file `Mathlib.SetTheory.ZFC.Class` defines `ZFClass` with the class constructions `ZFClass.powerset`, `ZFClass.sUnion` and `ZFClass.sInter`, the conversions `ZFClass.congToClass` and `ZFClass.classToCong` between classes and collections of classes, and the choice function. It also proves `ZFSet.coeEquiv : ZFSet ≃ {s : Set ZFSet // Small s}`: a class is a set exactly when it is small. Section 3 uses this. The file `Mathlib.SetTheory.ZFC.Ordinal` has the theory of transitive sets (closed under union, intersection, power set and union of a set of transitive sets) and of von Neumann ordinals. The files `Mathlib.SetTheory.ZFC.Rank` and `Mathlib.SetTheory.ZFC.VonNeumann` have the rank of pre-sets and sets and the hierarchy. The file `Mathlib.SetTheory.ZFC.Cardinal` has `ZFSet.card` with its lemmas for the empty set, insertion, pairs, unions, images and power sets.

Common errors of a learner:

- `x ∈ A` for `x : ZFSet` and `A : ZFClass` is membership of a set in a class. Membership of a class in a class is `A ᶜ∈ B`, a different relation with a scoped notation.
- The order on `{x // IsOrdinal x}` in `Ordinal.toZFSetIso` is inclusion. For von Neumann ordinals, `x ⊆ y` is equivalent to `x = y ∨ x ∈ y`.
- `ZFSet.rank x` is an ordinal of the same universe as `x`, while `WellFounded.rank` on the type `ZFSet.{u}` is in the universe above. The lemma `ZFSet.rank_eq_wfRank` contains a `lift`.

See the reference table for the full list.

### Exercises

1. (A) Prove that $\overline{2} = V_2$ and that $\overline{3} \neq V_3$. Give an element of $V_3$ that is not an ordinal.
2. (A) Prove that the union and the intersection of two transitive sets are transitive, and that $x$ is transitive if and only if $\bigcup x \subseteq x$.
3. (A) Compute $\mathrm{rank}(\{\emptyset, \{\{\emptyset\}\}\})$ from the definition, and check the result with part 3 of the theorem on rank.
4. (B) Prove that if $x$ is transitive, then $\mathcal{P}(x)$ is transitive. Deduce by induction that each $V_\alpha$ is transitive.
5. (B) Prove that $\overline{o} \cup \{\overline{o}\}$ is an ordinal for each ordinal $\overline{o}$, and that the union of a set of ordinals is an ordinal. Identify the union with a supremum of ordinals in the sense of Chapter 2.
6. (B) Show that $\mathrm{rank}(x) = \alpha$ if and only if $x \in V_{\alpha+1} \setminus V_\alpha$. Count the sets of rank exactly $3$.
7. (B) Prove that $V_\omega$ is countable, from the size theorem or directly: show that each element of $V_\omega$ is finite and that $V_n$ is finite for each $n$.
8. (C) Let $\kappa$ be an inaccessible cardinal (Chapter 6), viewed as its initial ordinal. Prove by induction on $\alpha < \kappa$ that $|V_\alpha| < \kappa$, and deduce that each $x \in V_\kappa$ has $|x| < \kappa$. This is the first step toward the fact that $V_\kappa$ is a model of ZFC, and Section 3 returns to it.

### Notes and history

The definition of the ordinals as transitive sets well-ordered by membership is due to von Neumann, in 1923. Burali-Forti published the paradox of the set of all ordinals in 1897. The cumulative hierarchy appears in Zermelo's paper of 1930 on the models of set theory. For a textbook account see Kunen, *Set Theory*, and Jech, *Set Theory*, Chapters 2 and 6.

### Reference

<?reference?>
