---
title: Hall's marriage theorem
kind: theory
modules:
  - Mathlib.Combinatorics.Hall.Basic
  - Mathlib.Combinatorics.Hall.Finite
explains:
  E3: [Finset.all_card_le_biUnion_card_iff_exists_injective, HallMarriageTheorem.hall_hard_inductive, Fintype.all_card_le_rel_image_card_iff_exists_injective, hallMatchingsFunctor]
  E2: [Fintype.all_card_le_filter_rel_iff_exists_injective, hallMatchingsOn, hallMatchingsOn.nonempty, hallMatchingsOn.restrict, Finset.all_card_le_biUnion_card_iff_existsInjective', HallMarriageTheorem.hall_hard_inductive_step_A, HallMarriageTheorem.hall_hard_inductive_step_B, HallMarriageTheorem.hall_cond_of_erase, HallMarriageTheorem.hall_cond_of_compl, HallMarriageTheorem.hall_cond_of_restrict]
  E1: auto
families: []
requires: [V30.C01, V03.C03, V03.C04, V13.C05, V24.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Hall's marriage theorem

### Overview

A family of finite sets $t(1), \dots, t(n)$ is given. The task is to choose one element from each set, with all the chosen elements distinct. Such a choice is a *system of distinct representatives*. The assignment of workers to jobs is a problem of this form.

There is an obvious necessary condition. Any $k$ of the sets must together contain at least $k$ elements, because the $k$ representatives are distinct elements of their union. Hall's theorem says that this condition is also sufficient. The condition is a statement about all subfamilies, and the conclusion is the existence of one choice function.

This section proves the finite theorem by the induction of Halmos and Vaughan. Then it proves the theorem for an infinite family of finite sets by compactness, as Mathlib does. Section 2 applies the theorem to matchings in bipartite graphs.

### Definitions

**Definition (System of distinct representatives).** Let $\iota$ and $\alpha$ be types and $t : \iota \to \mathrm{Finset}\ \alpha$ a family of finite sets. A *system of distinct representatives* for $t$ is an injective map $f : \iota \to \alpha$ with $f(i) \in t(i)$ for each $i \in \iota$.

For a finite set $s \subseteq \iota$ write $N(s) = \bigcup_{i \in s} t(i)$. This is the *neighbourhood* of $s$. In the language of graphs, $t$ is a bipartite graph between $\iota$ and $\alpha$, and $N(s)$ is the set of neighbours of $s$.

**Definition (Hall's condition).** The family $t$ satisfies *Hall's condition* if $|s| \le |N(s)|$ for each finite set $s \subseteq \iota$.

The condition for $s = \emptyset$ is empty. For $s = \{i\}$ the condition says $t(i) \ne \emptyset$.

**Proposition (Necessity).** If $t$ has a system of distinct representatives, then $t$ satisfies Hall's condition.

*Proof.* Let $f$ be a system of distinct representatives and $s$ a finite subset of $\iota$. The map $f$ sends $s$ into $N(s)$, since $f(i) \in t(i) \subseteq N(s)$ for $i \in s$. The map is injective, so $|s| = |f(s)| \le |N(s)|$. $\square$

Mathlib writes $N(s)$ as `s.biUnion t`, the union of a family of finsets indexed by a finset. The definition `Finset.biUnion` is in Volume 3, Chapter 3.

### Theorems and proofs

**Theorem (Hall, finite form).** Let $\iota$ be finite and $t : \iota \to \mathrm{Finset}\ \alpha$. If $t$ satisfies Hall's condition, then $t$ has a system of distinct representatives.

*Proof.* The proof is by strong induction on $n = |\iota|$. If $n = 0$, the empty map is a system of distinct representatives. Suppose $n \ge 1$ and suppose the theorem holds for each family with fewer than $n$ indices. There are two cases.

*Case A: each nonempty proper subset has surplus.* Suppose $|s| < |N(s)|$ for each $s$ with $\emptyset \ne s \ne \iota$. Pick an index $x$. Hall's condition for $\{x\}$ gives an element $a \in t(x)$. On $\iota' = \iota \setminus \{x\}$ define the family $t'(y) = t(y) \setminus \{a\}$. Let $s' \subseteq \iota'$. If $s' = \emptyset$, Hall's condition for $s'$ is empty. Otherwise $s'$ is a nonempty proper subset of $\iota$, because it does not contain $x$. So $|N(s')| \ge |s'| + 1$. The neighbourhood of $s'$ for $t'$ is $N(s') \setminus \{a\}$, and it has at least $|N(s')| - 1 \ge |s'|$ elements. Thus $t'$ satisfies Hall's condition, and it has $n - 1$ indices. The induction hypothesis gives an injective $f' : \iota' \to \alpha$ with $f'(y) \in t(y)$ and $f'(y) \ne a$. Put $f(x) = a$ and $f(y) = f'(y)$ for $y \ne x$. Then $f(i) \in t(i)$ for each $i$. The map $f$ is injective, because $f'$ is injective and $a$ is not a value of $f'$.

*Case B: some nonempty proper subset is tight.* Suppose $|s| = |N(s)|$ for some $s$ with $\emptyset \ne s \ne \iota$. Both $s$ and its complement $s^c$ have fewer than $n$ elements.

First consider the family $t$ restricted to $s$. Each subset of $s$ is a subset of $\iota$, so the restricted family satisfies Hall's condition. By the induction hypothesis there is an injective $g : s \to \alpha$ with $g(i) \in t(i)$ for $i \in s$. Its values lie in $N(s)$.

Next consider the family $t''(y) = t(y) \setminus N(s)$ for $y \in s^c$. Let $s'' \subseteq s^c$. The neighbourhood of $s''$ for $t''$ is $N(s'') \setminus N(s) = N(s \cup s'') \setminus N(s)$. The sets $s$ and $s''$ are disjoint, and $N(s) \subseteq N(s \cup s'')$. Hall's condition for $s \cup s''$ gives
$$|N(s'') \setminus N(s)| = |N(s \cup s'')| - |N(s)| \ge |s| + |s''| - |s| = |s''|.$$
So $t''$ satisfies Hall's condition. The induction hypothesis gives an injective $h : s^c \to \alpha$ with $h(y) \in t(y)$ and $h(y) \notin N(s)$.

Define $f$ as $g$ on $s$ and as $h$ on $s^c$. Then $f(i) \in t(i)$ for each $i$. The values of $g$ lie in $N(s)$ and the values of $h$ lie outside $N(s)$, so no value of $g$ equals a value of $h$. Both $g$ and $h$ are injective, so $f$ is injective. $\square$

The two cases cover all possibilities, since Hall's condition gives $|s| \le |N(s)|$ for each $s$. The case $n = 1$ falls under Case A, because a set with one element has no nonempty proper subset.

::: mathlib
`HallMarriageTheorem.hall_hard_inductive` · `Mathlib.Combinatorics.Hall.Finite`

The hard direction for `[Finite ι]`, with the hypothesis `∀ s : Finset ι, s.card ≤ (s.biUnion t).card`. The lemmas `hall_hard_inductive_step_A` and `hall_hard_inductive_step_B` are the two cases above. The lemmas `hall_cond_of_erase`, `hall_cond_of_restrict` and `hall_cond_of_compl` prove Hall's condition for the three smaller families.

<?decl HallMarriageTheorem.hall_hard_inductive?>
:::

The finite theorem extends to infinite index sets, as long as each $t(i)$ is finite.

**Theorem (Hall, infinite form).** Let $\iota$ be any type and $t : \iota \to \mathrm{Finset}\ \alpha$. If $t$ satisfies Hall's condition, then $t$ has a system of distinct representatives.

*Proof.* Give each finite set $t(i)$ the discrete topology. The product $X = \prod_{i \in \iota} t(i)$ is the set of maps $f$ with $f(i) \in t(i)$ for each $i$. Each factor is finite and discrete, hence compact. By Tychonoff's theorem (Volume 13, Chapter 5) the product $X$ is compact.

For a finite set $F \subseteq \iota$ let $C_F \subseteq X$ be the set of maps $f \in X$ whose restriction to $F$ is injective. It is a finite union of the open and closed sets $\{f : f(i) = a_i \text{ for } i \in F\}$, so it is closed.

The set $C_F$ is nonempty. Indeed, the family $t$ restricted to $F$ satisfies Hall's condition, so the finite theorem gives an injective $g$ on $F$ with $g(i) \in t(i)$. Each $t(j)$ is nonempty, so $g$ extends to an element of $X$ in $C_F$.

The family of closed sets $C_F$ has the finite intersection property. For finite sets $F_1, \dots, F_k$, the set $C_{F_1 \cup \dots \cup F_k}$ is nonempty and lies in each $C_{F_j}$. A compact space has no family of closed sets with the finite intersection property and empty intersection. So some $f$ lies in every $C_F$. For $i \ne j$ the map $f$ is injective on $\{i, j\}$, so $f(i) \ne f(j)$. Thus $f$ is a system of distinct representatives. $\square$

Mathlib runs the same argument as an inverse system. For finite $F \subseteq \iota$, the set $M(F)$ of injective maps $g : F \to \alpha$ with $g(i) \in t(i)$ is finite and nonempty, and restriction maps $M(F') \to M(F)$ for $F \subseteq F'$. A compatible choice of $g_F \in M(F)$ for all $F$, a *section*, exists by compactness, and its maps glue to one map on $\iota$.

::: mathlib
`hallMatchingsFunctor` · `Mathlib.Combinatorics.Hall.Basic`

`hallMatchingsFunctor t : (Finset ι)ᵒᵖ ⥤ Type (max u v)`. Its value at `ι'` is the subtype of `hallMatchingsOn t ι'`, the set of injective maps `f : ι' → α` with `f x ∈ t x`. The map on morphisms is `hallMatchingsOn.restrict`. The lemma `hallMatchingsOn.nonempty` proves that each value is nonempty, by the finite theorem.

<?decl hallMatchingsFunctor?>
:::

::: mathlib
`nonempty_sections_of_finite_inverse_system` · `Mathlib.CategoryTheory.CofilteredSystem`

For a directed preorder `J` and a functor `F : Jᵒᵖ ⥤ Type v` whose values are finite and nonempty, `F.sections.Nonempty`. It is a form of König's lemma on infinite trees.

<?decl nonempty_sections_of_finite_inverse_system?>
:::

::: mathlib
`Finset.all_card_le_biUnion_card_iff_exists_injective` · `Mathlib.Combinatorics.Hall.Basic`

The full theorem for any `ι`: `(∀ s : Finset ι, s.card ≤ (s.biUnion t).card) ↔ ∃ f, Function.Injective f ∧ ∀ x, f x ∈ t x`. The hard direction uses `hallMatchingsFunctor` and `nonempty_sections_of_finite_inverse_system`. The variant `Finset.all_card_le_biUnion_card_iff_existsInjective'` assumes `[Finite ι]` and needs only the induction.

<?decl Finset.all_card_le_biUnion_card_iff_exists_injective?>
:::

The hypothesis that each $t(i)$ is finite cannot be dropped.

**Example (An infinite set breaks the theorem).** Let $\iota = \alpha = \mathbb{N}$, $t(0) = \{1, 2, 3, \dots\}$ and $t(n) = \{n\}$ for $n \ge 1$. Let $s \subseteq \mathbb{N}$ be finite. If $0 \notin s$, then $N(s) = s$ and $|N(s)| = |s|$. If $0 \in s$, then $N(s)$ is infinite. So Hall's condition holds. But a system of distinct representatives must have $f(n) = n$ for $n \ge 1$, and then $f(0) = m \ge 1$ equals $f(m)$. No such $f$ exists.

### Examples

**Example (Three small families).** Let $t(1) = \{1, 2\}$, $t(2) = \{1, 2\}$ and $t(3) = \{1, 2, 3\}$. Hall's condition holds. A system of distinct representatives is $f(1) = 1$, $f(2) = 2$, $f(3) = 3$. The proof finds it by Case B: the set $s = \{1, 2\}$ is tight, with $N(s) = \{1, 2\}$. It matches $s$ inside $\{1,2\}$ and then matches $3$ in $t(3) \setminus \{1, 2\} = \{3\}$.

For $t(1) = \{1\}$ and $t(2) = t(3) = \{1, 2\}$, the whole family has $N = \{1, 2\}$, so Hall's condition fails.

**Example (Regular bipartite graphs).** Let $\iota$ and $\alpha$ be finite, and suppose there is $k \ge 1$ with $|t(i)| = k$ for each $i$ and with each $a \in \alpha$ in exactly $k$ of the sets $t(i)$. Let $s \subseteq \iota$ and count the pairs $(i, a)$ with $i \in s$ and $a \in t(i)$. There are $k|s|$ such pairs. Each pair has $a \in N(s)$, and each $a$ occurs in at most $k$ pairs. So $k|s| \le k|N(s)|$, and $|s| \le |N(s)|$. Hall's theorem gives a system of distinct representatives. The count is double counting, as in Volume 3, Chapter 6.

**Example (Latin rectangles).** A $k \times n$ *Latin rectangle* is a $k \times n$ array with entries in $\{1, \dots, n\}$ in which no row and no column contains an entry twice. Let $k < n$. Then each $k \times n$ Latin rectangle extends by one row to a $(k+1) \times n$ Latin rectangle. Let $t(j)$ be the set of symbols that do not occur in column $j$. It has $n - k$ elements. Each symbol occurs once in each row, so it occurs in exactly $k$ columns and is missing from exactly $n - k$ columns. The previous example with the constant $n - k \ge 1$ gives an injective choice $f(j) \in t(j)$. The new row $f(1), \dots, f(n)$ has distinct entries, and each column stays free of repeats. By induction, each Latin rectangle extends to a Latin square.

::: mathlib
`Fintype.all_card_le_rel_image_card_iff_exists_injective` · `Mathlib.Combinatorics.Hall.Basic`

For `R : SetRel α β` with a `Fintype` instance on `R.image {a}` for each `a`, the statement `(∀ A : Finset α, A.card ≤ Fintype.card (R.image A)) ↔ ∃ f, Function.Injective f ∧ ∀ x, (x, f x) ∈ R`. The variant `Fintype.all_card_le_filter_rel_iff_exists_injective` takes a decidable `r : α → β → Prop` with `[Fintype β]`.

<?decl Fintype.all_card_le_rel_image_card_iff_exists_injective?>
:::

### The library around it

The file `Hall.Finite` proves the theorem for a finite index type by induction. The file `Hall.Basic` adds the compactness step and the relation forms.

The graph form of Hall's theorem is in `Mathlib.Combinatorics.SimpleGraph.Hall`, and Section 2 explains it. It uses sets and `Set.ncard` instead of finsets, because a bipartite graph in Mathlib is a simple graph on one vertex type with a chosen pair of parts.

Birkhoff's theorem says that the doubly stochastic matrices are the convex hull of the permutation matrices. Its usual proof applies Hall's theorem to the support of the matrix, and Exercise 7 is its integer form. Mathlib has the theorem in the analysis library.

::: mathlib
`doublyStochastic_eq_convexHull_permMatrix` · `Mathlib.Analysis.Convex.Birkhoff`

Over a linearly ordered field `R` and a finite index type `n`, the set `doublyStochastic R n` equals the convex hull of the permutation matrices. Its home is the volume on convexity; it appears here as an application of matchings.

<?decl doublyStochastic_eq_convexHull_permMatrix?>
:::

The index of this edition has no declaration for the deficiency form of Hall's theorem or for the extension of Latin rectangles. Exercise 5 treats the first on paper, and the Latin rectangle example above treats the second.

### Exercises

1. (A) Let $t(1) = \{a, b\}$, $t(2) = \{b, c\}$, $t(3) = \{a, c\}$, $t(4) = \{a, b, c, d\}$. Check Hall's condition and find all systems of distinct representatives. Hint: $f(4) = d$ in each of them.
2. (A) Show that Hall's condition for $s$ and for $s'$ does not imply it for $s \cup s'$ in general. Hint: take $t(1) = t(2) = \{a\}$.
3. (A) In a group of $n$ students each student likes at least one of $n$ projects. Show by an example that this does not ensure that each student gets a different liked project, and state the condition that does.
4. (B) Let $G$ be a finite group and $H$ a subgroup. Show that there is a set of representatives of the left cosets of $H$ that is also a set of representatives of the right cosets. Hint: let $t(gH)$ be the set of right cosets that meet $gH$. A union of $k$ left cosets has $k|H|$ elements and lies in the union of the right cosets that meet it.
5. (B) Let $d \ge 0$. Show that a finite family $t$ has an injective partial choice on all but $d$ indices if and only if $|s| - |N(s)| \le d$ for each $s$. Hint: add $d$ new elements to $\alpha$ and to each $t(i)$.
6. (B) Find the step of the proof of the infinite form that fails for the example with $t(0) = \{1, 2, 3, \dots\}$.
7. (B) A $0$-$1$ matrix of size $n \times n$ has exactly $k \ge 1$ ones in each row and in each column. Show that it is a sum of $k$ permutation matrices. Hint: induction on $k$ with the regular bipartite example.
8. (C) Suppose that the finite family $t$ satisfies Hall's condition and $|t(i)| \ge k$ for each $i$, with $1 \le k \le |\iota|$. Show that $t$ has at least $k!$ systems of distinct representatives. Deduce that there are at least $n!\,(n-1)! \cdots 2!\,1!$ Latin squares of order $n$. Hint: in Case A there are $k$ choices of $a$, each giving a family with sets of size at least $k - 1$. In Case B the tight set $s$ has $|s| = |N(s)| \ge k$.

### Notes and history

Philip Hall proved the theorem in 1935 in "On representatives of subsets". Halmos and Vaughan gave the short induction above in 1950 in "The marriage problem", where the sets are the acquaintances of each woman among the men. Marshall Hall Jr. extended the theorem in 1948 to infinite families of finite sets. The compactness proof through an inverse system is the form that the Mathlib file follows, and the source cites Halpern (1966) for it. König's theorem on bipartite graphs (1931), in Section 2, is an equivalent result.

The files `Hall.Basic` and `Hall.Finite` list Alena Gusakov, Bhavik Mehta and Kyle Miller as authors.

### Reference

<?reference?>
