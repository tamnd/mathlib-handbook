---
title: Heyting algebras
kind: api
modules:
  - Mathlib.Order.Heyting.Basic
  - Mathlib.Order.Heyting.Boundary
  - Mathlib.Order.Heyting.Regular
  - Mathlib.Order.Heyting.Hom
explains:
  E2: [himp_himp, himp_inf_distrib, compl_sup_distrib, le_compl_compl, compl_compl_compl, LinearOrder.toBiheytingAlgebra, Heyting.isRegular_compl, Heyting.Regular.coe_sup, Coheyting.hnot_hnot_sup_boundary, map_compl]
  E1: auto
families: []
requires: [V04.C01, V04.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Heyting algebras

### Overview

Section 2 ends with the definition of a Heyting algebra: a bounded lattice with an implication $a \Rightarrow b$ such that $x \le (a \Rightarrow b)$ if and only if $x \sqcap a \le b$. It proves that each Heyting algebra is distributive, and it shows that the open sets of $\mathbb{R}$ form a Heyting algebra that is not Boolean. The four modules of this section hold the library for these algebras: the classes, the calculus of the implication and the pseudo-complement, the dual notion of a co-Heyting algebra with its boundary operator, the Boolean algebra of the regular elements, and the homomorphisms.

A Heyting algebra is the algebra of intuitionistic logic, in the same way that a Boolean algebra is the algebra of classical logic. Read $\le$ as "proves", $\sqcap$ as "and", $\sqcup$ as "or" and $\Rightarrow$ as "implies". The axiom then says that $x$ proves "$a$ implies $b$" exactly when $x$ and $a$ together prove $b$. Many lemmas about complements in Mathlib are stated for Heyting algebras, so this section is also the place where many lemmas used for Boolean algebras and for sets live.

### The library around it

**The classes.** The module `Mathlib.Order.Heyting.Basic` defines five classes. `GeneralizedHeytingAlgebra` is a lattice with a top and an operation `⇨` with the axiom `le_himp_iff`: $a \le (b \Rightarrow c) \iff a \sqcap b \le c$. `HeytingAlgebra` adds a bottom and the pseudo-complement `ᶜ`, with the axiom `himp_bot`: $a \Rightarrow \bot = a^c$. The dual notions are `GeneralizedCoheytingAlgebra`, a lattice with a bottom and a difference `\` with the axiom `sdiff_le_iff`: $a \setminus b \le c \iff a \le b \sqcup c$, and `CoheytingAlgebra`, which adds a top and the Heyting negation `hnot`, written with a prefix symbol, and the lemma `top_sdiff'` states its axiom: $\top \setminus a$ is the negation of $a$. This section writes ${\sim} a$ for this negation. A `BiheytingAlgebra` has both structures. The distributive law is the instance `GeneralizedHeytingAlgebra.toDistribLattice`, with the proof of Section 2.

The instances cover the standard examples. `Prop.instHeytingAlgebra` makes the propositions a Heyting algebra, with `himp_iff_imp` and `compl_iff_not` as the formulas. Products and families have `Prod.instHeytingAlgebra` and `Pi.instHeytingAlgebra`, with the operations computed in each coordinate. The order dual of a Heyting algebra is a co-Heyting algebra by `OrderDual.instCoheytingAlgebra`, and the converse is `OrderDual.instHeytingAlgebra`. Each Boolean algebra is a bi-Heyting algebra by `BooleanAlgebra.toBiheytingAlgebra`, and each generalized Boolean algebra, such as the finite sets of a type, is a generalized co-Heyting algebra by `GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra`. The complete Heyting algebras of Chapter 4 are the frames, `Order.Frame`.

A structure can be built from less data. `HeytingAlgebra.ofHImp` takes a distributive bounded lattice and an operation with the property of `le_himp_iff`, and `HeytingAlgebra.ofCompl` takes a complement $c$ with $a \le c(b) \sqcup d \iff a \sqcap b \le d$. The dual constructors are `CoheytingAlgebra.ofSDiff` and `CoheytingAlgebra.ofHNot`. To move a structure along an injective map that commutes with the operations, use `Function.Injective.heytingAlgebra`, and along an equivalence, use `Equiv.heytingAlgebra`.

**Linear orders.** A bounded linear order is a bi-Heyting algebra by `LinearOrder.toBiheytingAlgebra`, with
$$a \Rightarrow b = \begin{cases} \top & a \le b, \\ b & a > b. \end{cases}$$
*Proof of the axiom.* If $a \le b$, then $x \le \top$ and $x \sqcap a \le a \le b$ both hold for each $x$. If $a > b$, then $x \sqcap a = \min(x, a) \le b$ holds if and only if $x \le b$, because $a \le b$ is false. So both sides of `le_himp_iff` are the statement $x \le b$. $\square$

**The calculus of the implication.** The axiom has a direct consequence that gives most identities: two elements are equal when they have the same lower bounds. The table lists the main identities.

| Lean name | Statement |
|---|---|
| `himp_self` | $a \Rightarrow a = \top$ |
| `himp_eq_top_iff` | $a \Rightarrow b = \top \iff a \le b$ |
| `inf_himp_le` | $a \sqcap (a \Rightarrow b) \le b$ |
| `himp_himp` | $a \Rightarrow (b \Rightarrow c) = (a \sqcap b) \Rightarrow c$ |
| `himp_inf_distrib` | $a \Rightarrow (b \sqcap c) = (a \Rightarrow b) \sqcap (a \Rightarrow c)$ |
| `sup_himp_distrib` | $(a \sqcup b) \Rightarrow c = (a \Rightarrow c) \sqcap (b \Rightarrow c)$ |
| `himp_triangle` | $(a \Rightarrow b) \sqcap (b \Rightarrow c) \le a \Rightarrow c$ |
| `le_himp_himp` | $a \le (a \Rightarrow b) \Rightarrow b$ |

The implication is monotone in its second argument, `himp_le_himp_left`, and antitone in its first argument, `himp_le_himp_right`. *Proof of `himp_himp`.* For each $x$: $x \le a \Rightarrow (b \Rightarrow c)$ holds if and only if $x \sqcap a \le b \Rightarrow c$, if and only if $x \sqcap a \sqcap b \le c$, if and only if $x \le (a \sqcap b) \Rightarrow c$. Two elements with the same lower bounds are equal. $\square$ *Proof of `himp_inf_distrib`.* $x \le a \Rightarrow (b \sqcap c)$ holds if and only if $x \sqcap a \le b \sqcap c$, that is $x \sqcap a \le b$ and $x \sqcap a \le c$, that is $x \le a \Rightarrow b$ and $x \le a \Rightarrow c$. $\square$

**The pseudo-complement.** The pseudo-complement $a^c = a \Rightarrow \bot$ is the largest element disjoint from $a$, by `le_compl_iff_disjoint_right`. It is antitone, `compl_anti`, and `compl_bot` and `compl_top` give its values at the bounds. One law of De Morgan holds, `compl_sup_distrib`: $(a \sqcup b)^c = a^c \sqcap b^c$. *Proof.* This is `sup_himp_distrib` with $c = \bot$. $\square$ The other law holds only in one direction, `compl_sup_compl_le`: $a^c \sqcup b^c \le (a \sqcap b)^c$. The double complement is a closure: `le_compl_compl` says $a \le a^{cc}$, and `compl_compl_compl` says $a^{ccc} = a^c$. *Proof.* $a \le a^{cc}$ means $a \sqcap a^c \le \bot$, and this is `inf_himp_le` with $b = \bot$. Apply this to $a^c$ to get $a^c \le a^{ccc}$. Apply the antitone map $x \mapsto x^c$ to $a \le a^{cc}$ to get $a^{ccc} \le a^c$. $\square$ The double complement also commutes with $\sqcap$ and with $\Rightarrow$, by `compl_compl_inf_distrib` and `compl_compl_himp_distrib`. The lemma `compl_compl` of Section 2, $a^{cc} = a$, needs a Boolean algebra, and it fails for the open sets of $\mathbb{R}$: the open set $\mathbb{R} \setminus \{0\}$ has pseudo-complement $\emptyset$ and double pseudo-complement $\mathbb{R}$.

**Co-Heyting algebras and the boundary.** Each lemma above has a dual for the difference and the negation, with `sdiff` in place of `himp` and `hnot` in place of `compl`. Examples are `sdiff_sdiff_left`, $(a \setminus b) \setminus c = a \setminus (b \sqcup c)$, `sup_hnot_self`, $a \sqcup {\sim} a = \top$, `hnot_inf_distrib`, and `hnot_hnot_le`, ${\sim}{\sim} a \le a$. In a bi-Heyting algebra the two negations compare by `compl_le_hnot`. The closed sets of a topological space form a co-Heyting algebra: $s \setminus t$ is the closure of the set difference, and ${\sim} s$ is the closure of the complement of $s$.

The module `Mathlib.Order.Heyting.Boundary` defines the boundary `Coheyting.boundary` of an element of a co-Heyting algebra: $\partial a = a \sqcap {\sim} a$. The prefix notation `∂` is in the scope `Heyting`. For a closed set $s$ this is $s$ minus its interior, the topological boundary. The lemmas are `Coheyting.boundary_le`, $\partial a \le a$, `Coheyting.boundary_boundary`, $\partial \partial a = \partial a$, the Leibniz rule `Coheyting.boundary_inf`, $\partial (a \sqcap b) = (\partial a \sqcap b) \sqcup (a \sqcap \partial b)$, and `Coheyting.boundary_sup_le`. In a Boolean algebra each boundary is $\bot$, by `Coheyting.boundary_eq_bot`. The decomposition `Coheyting.hnot_hnot_sup_boundary` says ${\sim}{\sim} a \sqcup \partial a = a$. *Proof.* By distributivity, ${\sim}{\sim} a \sqcup (a \sqcap {\sim} a) = ({\sim}{\sim} a \sqcup a) \sqcap ({\sim}{\sim} a \sqcup {\sim} a)$. The first factor is $a$, because ${\sim}{\sim} a \le a$. The second factor is $\top$, by `sup_hnot_self` for ${\sim} a$. $\square$

**Regular elements.** The module `Mathlib.Order.Heyting.Regular` studies the elements with $a^{cc} = a$. The predicate is `Heyting.IsRegular`, and `Heyting.IsRegular.eq` extracts the equation. Each pseudo-complement is regular, `Heyting.isRegular_compl`, which is `compl_compl_compl`. The regular elements are closed under $\sqcap$ and $\Rightarrow$, by `Heyting.IsRegular.inf` and `Heyting.IsRegular.himp`, and $\bot$ and $\top$ are regular. They are not closed under $\sqcup$. The subtype `Heyting.Regular α` has the coercion `Heyting.Regular.val`, and the map `Heyting.Regular.toRegular` sends $a$ to $a^{cc}$, by `Heyting.Regular.coe_toRegular`. The two maps form a Galois insertion, `Heyting.Regular.gi`, of the kind that Chapter 6 studies. The supremum of two regular elements is the double complement of their supremum in $\alpha$, `Heyting.Regular.coe_sup`: $a \sqcup_{\mathrm{reg}} b = (a \sqcup b)^{cc}$. *Proof.* An upper bound $c$ of $a$ and $b$ that is regular satisfies $a \sqcup b \le c$, so $(a \sqcup b)^{cc} \le c^{cc} = c$. And $(a \sqcup b)^{cc}$ is regular and above $a \sqcup b$. $\square$ With this supremum, `Heyting.Regular.instBooleanAlgebra` makes `Heyting.Regular α` a Boolean algebra. This is the algebraic form of the double negation translation of classical logic into intuitionistic logic. For the open sets of $\mathbb{R}$ the regular elements are the regular open sets, the interiors of closed sets. The constructor `BooleanAlgebra.ofRegular` turns a Heyting algebra in which each $a \sqcup a^c$ is regular into a Boolean algebra. A decidable proposition is regular, by `Heyting.isRegular_of_decidable`, and each element of a Boolean algebra is regular, by `Heyting.isRegular_of_boolean`.

**Homomorphisms.** The module `Mathlib.Order.Heyting.Hom` adds three types to the family of Section 4. `HeytingHom α β` is a lattice homomorphism that keeps $\bot$ and $\Rightarrow$, with class `HeytingHomClass` and axiom `HeytingHomClass.map_himp`. `CoheytingHom α β` keeps $\top$ and $\setminus$, with axiom `CoheytingHomClass.map_sdiff`, and `BiheytingHom α β` keeps both operations. Each has the API of Section 4: `HeytingHom.id`, `HeytingHom.comp`, `HeytingHom.ext`, `HeytingHom.copy`, `HeytingHom.coe_comp`, `HeytingHom.cancel_right`, and the forgetful map `HeytingHom.toLatticeHom`. A Heyting homomorphism keeps $\top$, because $\top = \bot \Rightarrow \bot$, so `HeytingHomClass.toBoundedLatticeHomClass` is an instance. It also keeps the pseudo-complement, `map_compl`. *Proof.* $f(a^c) = f(a \Rightarrow \bot) = f(a) \Rightarrow f(\bot) = f(a) \Rightarrow \bot = f(a)^c$. $\square$ The duals are `map_hnot` and `map_symmDiff`. Order isomorphisms are bi-Heyting homomorphisms by `OrderIsoClass.toBiheytingHomClass`. Between Boolean algebras each bounded lattice homomorphism is a bi-Heyting homomorphism, by `BoundedLatticeHomClass.toBiheytingHomClass`, because the implication $a \Rightarrow b = b \sqcup a^c$ is built from the lattice operations and the complement.

#### Common errors

1. The lemma `compl_compl` needs a Boolean algebra. In a Heyting algebra the available lemmas are `le_compl_compl` and `compl_compl_compl`. An attempt to use `compl_compl` on the open sets of a space fails at instance search.
2. The negation `hnot` of a co-Heyting algebra is not the pseudo-complement. In a bi-Heyting algebra that is not Boolean the two differ, the basic relation between them is `compl_le_hnot`, and a lemma about `ᶜ` does not apply to `hnot`.
3. `LinearOrder.toBiheytingAlgebra` is not an instance. Declare it with `letI` or as a local instance when a proof needs the implication of a bounded linear order.

### Exercises

1. (A) Prove `himp_eq_top_iff` from `le_himp_iff` and `top_le_iff`.
2. (A) In the bounded linear order $\{0, 1, 2\}$ compute $a \Rightarrow b$ and $a^c$ for all $a, b$, and find the regular elements.
3. (B) Prove `sup_himp_distrib` by the method of lower bounds, and deduce the law $(a \sqcup b)^c = a^c \sqcap b^c$.
4. (B) Give two open sets $U, V$ of $\mathbb{R}$ with $(U \cap V)^c \ne U^c \cup V^c$ in the Heyting algebra of open sets, where $W^c$ is the interior of the complement.
5. (B) Show that the regular elements of a Heyting algebra are not closed under $\sqcup$, with the open sets $(0, 1)$ and $(1, 2)$ of $\mathbb{R}$.
6. (C) Show that a Heyting algebra is a Boolean algebra if and only if each element is regular, and compare the result with `BooleanAlgebra.ofRegular`.

### Reference

<?reference?>
