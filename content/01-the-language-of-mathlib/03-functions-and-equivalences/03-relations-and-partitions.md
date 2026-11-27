---
title: Relations, equivalence relations and partitions
kind: theory
modules:
  - Mathlib.Logic.Relation
  - Mathlib.Basic.Rel
explains:
  E3: [Relation.EqvGen, Rel]
  E2: [SetRel, Relation.Comp, Relation.comp_assoc, Relation.ReflTransGen, Relation.ReflTransGen.trans, Relation.ReflTransGen.single, Relation.EqvGen.equivalence, Relation.EqvGen.mono, Equivalence.eqvGen_iff, Equivalence.comap, Relation.Map, Relation.eqvGen_eq_reflTransGen]
  E1: auto
families: []
requires: [V01.C02]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V01/C03/Examples.lean
  - MathlibHandbook/V01/C03/Exercises.lean
  - MathlibHandbook/V01/C03/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Relations, equivalence relations and partitions

### Overview

A relation compares two elements: $a < b$, $a \mid b$, $a \equiv b \pmod n$, "$a$ and $b$ have the same colour". A function is a special relation, one that relates each input to exactly one output. This section treats relations in general, and then the most important kind for the foundations: the *equivalence relations*. An equivalence relation says when two elements are "the same for the present purpose".

The main theorem is that equivalence relations on $\alpha$ correspond exactly to partitions of $\alpha$: ways to cut $\alpha$ into disjoint nonempty pieces. The section gives a complete proof of the correspondence. It also shows how to make an equivalence relation from an arbitrary relation, by the smallest equivalence relation that contains it. The next section uses equivalence relations to build quotient types.

### Definitions

**Definition (Relation).** A *relation* from $\alpha$ to $\beta$ is a function $r : \alpha \to \beta \to \mathrm{Prop}$. A relation on $\alpha$ is a relation from $\alpha$ to $\alpha$. The statement $r(a, b)$ is often written $a \mathrel{r} b$.

::: mathlib
`Rel` · `Mathlib.Basic.Rel`

`Rel α β` is an abbreviation for `α → β → Prop`. Most of Mathlib writes the function type directly, for example `r : α → α → Prop`, and the lemmas about relations take this form. The type `SetRel α β` is the other form, `Set (α × β)`, the set of related pairs. It suits relations that are treated as sets, for example in the theory of uniform spaces.

<?decl Rel?>
:::

**Definition (Properties of a relation).** A relation $r$ on $\alpha$ is:

1. *reflexive* when $\forall a,\ r(a, a)$;
2. *symmetric* when $\forall a\ b,\ r(a, b) \to r(b, a)$;
3. *transitive* when $\forall a\ b\ c,\ r(a, b) \to r(b, c) \to r(a, c)$;
4. *antisymmetric* when $\forall a\ b,\ r(a, b) \to r(b, a) \to a = b$;
5. an *equivalence relation* when it is reflexive, symmetric and transitive.

**Definition (Equivalence class).** Let $r$ be an equivalence relation on $\alpha$. The *class* of $a$ is the set $[a] = \{x \mid r(x, a)\}$. The set of all classes is $\{[a] \mid a : \alpha\}$, a term of `Set (Set α)`.

**Definition (Partition).** A *partition* of $\alpha$ is a set $P$ of subsets of $\alpha$ such that:

1. $\emptyset \notin P$;
2. for each $a : \alpha$ there is exactly one $B \in P$ with $a \in B$.

The elements of $P$ are the *blocks*. Condition 2 says that the blocks cover $\alpha$ and that two different blocks are disjoint.

**Definition (Kernel of a function).** For $f : \alpha \to \beta$, the *kernel* of $f$ is the relation $a \sim_f b \iff f(a) = f(b)$ on $\alpha$.

**Definition (Composition and closures).** For relations $r$ from $\alpha$ to $\beta$ and $s$ from $\beta$ to $\gamma$, the *composite* $r \circ s$ relates $a$ to $c$ when $\exists b,\ r(a, b) \land s(b, c)$. For a relation $r$ on $\alpha$:

1. the *reflexive transitive closure* $r^{*}$ is the inductive relation with the rules: $r^{*}(a, a)$; and if $r^{*}(a, b)$ and $r(b, c)$, then $r^{*}(a, c)$;
2. the *equivalence closure* $\mathrm{EqvGen}(r)$ is the inductive relation with four rules: $r(a, b)$ gives $\mathrm{EqvGen}(r)(a, b)$; it is reflexive; it is symmetric; it is transitive.

An inductive relation holds only when the rules force it. So $r^{*}(a, b)$ holds exactly when there is a finite chain $a = x_0 \mathrel{r} x_1 \mathrel{r} \cdots \mathrel{r} x_n = b$, with $n \geq 0$. A proof about an inductive relation uses induction on the rules.

::: mathlib
`Relation.EqvGen` · `Mathlib.Logic.Relation`

The constructors of `Relation.EqvGen r` are `rel`, `refl`, `symm` and `trans`, one for each rule. The lemma `Relation.EqvGen.equivalence` states that it is an equivalence relation. The reflexive transitive closure is `Relation.ReflTransGen`, with `Relation.ReflTransGen.single` and `Relation.ReflTransGen.trans`. The composite is `Relation.Comp`.

<?decl Relation.EqvGen?>
:::

### Theorems and proofs

**Theorem (Kernels are equivalence relations).** For every $f : \alpha \to \beta$, the kernel $\sim_f$ is an equivalence relation.

*Proof.* Equality on $\beta$ is reflexive, symmetric and transitive. Each property of $\sim_f$ is the same property of equality at the values $f(a)$, $f(b)$, $f(c)$. $\square$

**Theorem (Pullback of an equivalence relation).** Let $r$ be an equivalence relation on $\beta$ and $f : \alpha \to \beta$. Then $a \sim b \iff r(f(a), f(b))$ is an equivalence relation on $\alpha$.

*Proof.* The same argument as for the kernel, with $r$ in place of equality. $\square$

The kernel is the pullback of equality.

::: mathlib
`Equivalence.comap` · `Mathlib.Logic.Relation`

The statement is `Equivalence r → Equivalence (Function.onFun r f)`, where `Function.onFun r f a b = r (f a) (f b)`. The core structure `Equivalence r` has the fields `refl`, `symm` and `trans`. The bundled form, an equivalence relation stored with its proof, is `Setoid α`, and the kernel of `f` in that form is `Setoid.ker f`.

<?decl Equivalence.comap?>
:::

**Theorem (Classes).** Let $r$ be an equivalence relation on $\alpha$. For all $a, b : \alpha$:

1. $a \in [a]$;
2. $[a] = [b]$ if and only if $r(a, b)$;
3. $[a] = [b]$ or $[a] \cap [b] = \emptyset$.

*Proof.* 1. $r(a, a)$ by reflexivity.

2. Assume $[a] = [b]$. By part 1, $a \in [a] = [b]$, so $r(a, b)$. Conversely, assume $r(a, b)$. Let $x \in [a]$, so $r(x, a)$. Transitivity gives $r(x, b)$, so $x \in [b]$. Let $x \in [b]$, so $r(x, b)$. Symmetry gives $r(b, a)$, and transitivity gives $r(x, a)$. So $[a] = [b]$ by double inclusion.

3. By the excluded middle, $[a] \cap [b]$ is empty or it has an element $x$. In the second case $r(x, a)$ and $r(x, b)$. Symmetry and transitivity give $r(a, b)$, and part 2 gives $[a] = [b]$. $\square$

**Theorem (Equivalence relations and partitions).** Let $\alpha$ be a type.

1. If $r$ is an equivalence relation on $\alpha$, then the set $P_r$ of its classes is a partition of $\alpha$.
2. If $P$ is a partition of $\alpha$, then the relation $r_P(a, b) \iff$ "$a$ and $b$ lie in the same block" is an equivalence relation.
3. The two constructions are inverse to each other: $r_{P_r} = r$ and $P_{r_P} = P$.

So the equivalence relations on $\alpha$ are in bijection with the partitions of $\alpha$.

*Proof.* 1. Each class $[a]$ contains $a$, so $\emptyset \notin P_r$. Let $a : \alpha$. The class $[a]$ is a block that contains $a$. If $[b]$ is another block with $a \in [b]$, then $r(a, b)$, and part 2 of the theorem on classes gives $[b] = [a]$. So the block is unique.

2. Write $B(a)$ for the unique block that contains $a$. Then $r_P(a, b)$ holds exactly when $B(a) = B(b)$: if $a$ and $b$ lie in a block $B$, then uniqueness gives $B = B(a)$ and $B = B(b)$; conversely, $B(a)$ contains both. So $r_P$ is the kernel of the function $B : \alpha \to \texttt{Set}\ \alpha$, and it is an equivalence relation by the theorem on kernels.

3. For the first equation, fix $a, b$. The relation $r_{P_r}(a, b)$ holds when some class $[c]$ contains both $a$ and $b$. If $r(a, b)$, the class $[b]$ contains both. Conversely, if $r(a, c)$ and $r(b, c)$, then $r(a, b)$ by symmetry and transitivity. So $r_{P_r} = r$.

For the second equation, the class of $a$ for $r_P$ is $\{x \mid B(x) = B(a)\}$. This is the block $B(a)$: an element $x$ is in $B(a)$ if and only if $B(x) = B(a)$, by the uniqueness of the block of $x$. So the classes of $r_P$ are the sets $B(a)$ for $a : \alpha$. Every block of $P$ is of this form, because a block is nonempty and so contains some $a$, and then it equals $B(a)$. So $P_{r_P} = P$. $\square$

::: mathlib
`Setoid.classes_mkClasses` · `Mathlib.Order.Setoid.Partition`

Mathlib states the correspondence with bundled equivalence relations. The set of classes is `Setoid.classes r`, and `Setoid.isPartition_classes` is part 1. A partition gives the relation `Setoid.mkClasses c hc`, and the two lemmas `Setoid.classes_mkClasses` and `Setoid.mkClasses_classes` are part 3. The predicate `Setoid.IsPartition c` is `∅ ∉ c ∧ ∀ a, ∃! b ∈ c, a ∈ b`, the definition above. Volume 4 shows that the correspondence is an isomorphism of orders, `Setoid.Partition.orderIso`.

<?decl Setoid.classes_mkClasses?>
:::

**Theorem (The equivalence closure).** Let $r$ be a relation on $\alpha$. Then $\mathrm{EqvGen}(r)$ is an equivalence relation that contains $r$. If $s$ is any equivalence relation that contains $r$, then $\mathrm{EqvGen}(r) \subseteq s$. So $\mathrm{EqvGen}(r)$ is the smallest equivalence relation that contains $r$.

*Proof.* The first two claims are three of the four rules and the first rule. For the last claim, prove by induction on the rules that $\mathrm{EqvGen}(r)(a, b)$ implies $s(a, b)$. The rule $r(a, b)$ gives $s(a, b)$ because $s$ contains $r$. The rule of reflexivity gives $s(a, a)$ because $s$ is reflexive. For the rule of symmetry, the induction hypothesis gives $s(a, b)$, and symmetry of $s$ gives $s(b, a)$. For the rule of transitivity, the induction hypotheses give $s(a, b)$ and $s(b, c)$, and transitivity gives $s(a, c)$. $\square$

If $r$ is already an equivalence relation, then $\mathrm{EqvGen}(r) = r$: the theorem with $s = r$ gives one inclusion, and the first rule gives the other. This is `Equivalence.eqvGen_iff`.

**Theorem (Equivalence closure of a symmetric relation).** If $r$ is symmetric, then $\mathrm{EqvGen}(r) = r^{*}$.

*Proof.* $r^{*}$ contains $r$, is reflexive, and is transitive, by induction on the second argument. It is symmetric: by induction on $r^{*}(a, b)$, the case $a = b$ is reflexivity, and if $r^{*}(a, b)$ and $r(b, c)$, then $r(c, b)$ by symmetry of $r$, and the induction hypothesis $r^{*}(b, a)$ gives $r^{*}(c, a)$ by a chain that starts with the step $c \mathrel{r} b$. So $r^{*}$ is an equivalence relation that contains $r$, and $\mathrm{EqvGen}(r) \subseteq r^{*}$ by the previous theorem. Conversely, $r^{*} \subseteq \mathrm{EqvGen}(r)$ by induction on $r^{*}$: the base case is reflexivity, and the step is transitivity with one use of $r$. $\square$

So, for a symmetric relation, two elements are equivalent exactly when a finite chain of $r$ steps connects them. For a general relation, the chain may use steps in both directions.

::: mathlib
`Relation.eqvGen_eq_reflTransGen` · `Mathlib.Logic.Relation`

The statement is `[Std.Symm r] : Relation.EqvGen r = Relation.ReflTransGen r`. The symmetry is an instance argument. The older name `Symmetric` is deprecated to `Std.Symm` in this edition.

<?decl Relation.eqvGen_eq_reflTransGen?>
:::

### Examples

**Example (Congruence modulo $n$).** For $n \geq 1$, the relation $a \equiv b \pmod n \iff n \mid a - b$ on $\mathbb{Z}$ is the kernel of the function $a \mapsto a \bmod n$, the remainder in $\{0, \ldots, n - 1\}$. So it is an equivalence relation, by the theorem on kernels. Its classes are the $n$ residue classes $[0], [1], \ldots, [n - 1]$, and they form a partition of $\mathbb{Z}$. For $n = 2$, the blocks are the even and the odd integers.

**Example (Fractions).** On pairs $(a, b)$ of integers with $b \neq 0$, let $(a, b) \sim (c, d)$ when $ad = bc$. Reflexivity and symmetry are clear. For transitivity, let $ad = bc$ and $cf = de$. Multiply the first equation by $f$ and the second by $b$: $adf = bcf = bde$. So $d(af - be) = 0$, and $d \neq 0$ gives $af = be$. The cancellation of $d$ is the step that needs $d \neq 0$, and so the relation is only an equivalence relation on pairs with a nonzero second component.

**Example (Equivalence closure of the successor relation).** Let $r(a, b) \iff b = a + 1$ on $\mathbb{Z}$. Then $\mathrm{EqvGen}(r)$ relates every pair: for $a \leq b$, the chain $a, a + 1, \ldots, b$ uses $b - a$ steps of $r$, and for $a > b$ the symmetric rule reverses the chain. So $\mathrm{EqvGen}(r)$ has one class, $\mathbb{Z}$. The reflexive transitive closure $r^{*}$ is the order $a \leq b$, which is not symmetric.

**Counterexample (Closeness is not transitive).** On $\mathbb{R}$, let $a \approx b$ when $|a - b| \leq 1$. The relation is reflexive and symmetric. It is not transitive: $0 \approx 1$ and $1 \approx 2$, but $|0 - 2| = 2 > 1$. Its "classes" $\{x \mid x \approx a\} = [a - 1, a + 1]$ overlap without being equal, so they do not form a partition. The equivalence closure of $\approx$ has one class, $\mathbb{R}$: any two reals are joined by a finite chain of steps of length at most $1$.

### The library around it

The module `Mathlib.Logic.Relation` has the closures `Relation.ReflGen`, `Relation.TransGen`, `Relation.ReflTransGen` and `Relation.EqvGen`, the composite `Relation.Comp` with `Relation.comp_assoc`, and the image of a relation under a pair of functions, `Relation.Map`. The core library defines `Equivalence`. The order-theoretic properties of a relation are classes in `Mathlib.Order.Defs.Unbundled`, for example `IsTrans α r` and `IsAntisymm α r`, and Volume 4 uses them for orders.

The bundled equivalence relation `Setoid α` and the theory of partitions are in `Mathlib.Order.Setoid.Basic` and `Mathlib.Order.Setoid.Partition`. There, the equivalence relations on $\alpha$ form a complete lattice, ordered by inclusion, and `Setoid.eqvGen_eq` states that the equivalence closure is the infimum of the equivalence relations that contain $r$, which is the theorem above in the language of lattices.

#### Common errors

1. A learner proves reflexivity and symmetry and forgets transitivity. The counterexample above shows that it is a real condition.
2. A learner writes `r a b` for a `Setoid`. Use `s a b` through the coercion, or `a ≈ b` for the instance, or `Setoid.r`.
3. A learner tries to use an inductive closure as a function and unfold it. Use `induction h` on the proof `h : Relation.EqvGen r a b`.

### Exercises

1. (A) Decide which of the properties reflexive, symmetric, transitive and antisymmetric hold for $\leq$, $<$ and $\mid$ on $\mathbb{N}$, and for "$a$ and $b$ have a common prime factor".
2. (A) List all partitions of $\{1, 2, 3\}$. How many equivalence relations does $\{1, 2, 3\}$ have?
3. (B) Prove that the intersection of two equivalence relations is an equivalence relation, and show that the union need not be.
4. (B) Let $f : \alpha \to \beta$ be surjective. Prove that the blocks of the kernel of $f$ are in bijection with $\beta$.
5. (B) Prove that composition of relations is associative.
6. (B) Prove that $r^{*}$ is transitive, by induction on the second hypothesis.
7. (C) On $\mathbb{N} \times \mathbb{N}$, let $(a, b) \sim (c, d)$ when $a + d = b + c$. Prove that this is an equivalence relation, and describe its classes. The next section builds $\mathbb{Z}$ from it.
8. (C) Let $r$ be a reflexive and transitive relation on $\alpha$. Prove that $a \sim b \iff r(a, b) \land r(b, a)$ is an equivalence relation, and that $r$ induces an antisymmetric relation on its classes.

### Notes and history

Gauss introduced congruence modulo $n$ in the *Disquisitiones Arithmeticae* (1801), and the idea to calculate with classes of numbers comes from that book. The general notion of an equivalence relation and its classes appears in Frege's *Grundlagen* (1884), where the number of a set is defined as a class of sets under equinumerosity. The correspondence with partitions became standard in the set theory of the 1930s. The number of partitions of an $n$ element set is the Bell number $B_n$; Exercise 2 computes $B_3 = 5$.

### Reference

<?reference?>
