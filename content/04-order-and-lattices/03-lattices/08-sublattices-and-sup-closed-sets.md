---
title: Sublattices and sup-closed sets
kind: api
modules:
  - Mathlib.Order.SupClosed
  - Mathlib.Order.Sublattice
  - Mathlib.Order.LatticeIntervals
  - Mathlib.Order.Lattice.Congruence
explains:
  E2: [SupClosed, supClosure, latticeClosure, latticeClosure_sup_inf_induction, Sublattice, Sublattice.gc_map_comap, Set.Icc.isCompl_iff, LatticeCon, "LatticeCon.mk'"]
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

## Sublattices and sup-closed sets

### Overview

A subset $s$ of a lattice $\alpha$ is a sublattice when $a \sqcup b$ and $a \sqcap b$ are in $s$ for all $a, b \in s$. A sublattice is a lattice with the operations of $\alpha$. This is a stronger condition than "a subset that is a lattice for the induced order". In the lattice of the subsets of $\{1, 2, 3\}$, the set $\{\emptyset, \{1\}, \{2\}, \{1, 2, 3\}\}$ is a lattice for the induced order, with $\{1\} \sqcup \{2\} = \{1, 2, 3\}$. It is not a sublattice, because the union $\{1, 2\}$ is not in it.

The library splits the condition into its two halves. A set is sup-closed when it is closed under $\sqcup$, and inf-closed when it is closed under $\sqcap$. Each half has a closure operator: the smallest sup-closed set that contains a given set. There is a bundled structure of sublattices, with images and preimages along lattice homomorphisms. Two more modules complete the picture. The intervals $[a, b]$, $(-\infty, a]$ and $[a, \infty)$ of a lattice are sublattices, so they carry lattice instances. A congruence of a lattice is an equivalence relation that is compatible with $\sqcup$ and $\sqcap$, and its classes form the quotient lattice.

The section uses the lattices of Section 1 and the lattice homomorphisms of Section 4 of this chapter. The modules are `Mathlib.Order.SupClosed`, `Mathlib.Order.Sublattice`, `Mathlib.Order.LatticeIntervals` and `Mathlib.Order.Lattice.Congruence`.

### The library around it

#### Sup-closed and inf-closed sets

The predicate `SupClosed s` says that $a \sqcup b \in s$ for all $a, b \in s$, and `InfClosed s` is the dual. `IsSublattice s` is the conjunction of the two. These are unbundled predicates on `Set α`, in the style of `IsUpperSet`, so they work with each set operation of the library.

Some sets are sup-closed for a simple reason. In a linear order, $a \sqcup b$ is $a$ or $b$, so each set is sup-closed, `LinearOrder.supClosed`, and each set is a sublattice, `LinearOrder.isSublattice`. An upper set contains $a \sqcup b$ because $a \le a \sqcup b$, so `IsUpperSet.supClosed` holds. For a lower set $s$, `IsLowerSet.supClosed_iff_directedOn` says that $s$ is sup-closed if and only if it is directed: two elements of $s$ have an upper bound in $s$. In general, `SupClosed.directedOn` gives that a sup-closed set is directed.

The predicate is stable under the usual operations.

| Lean name | Statement |
|---|---|
| `supClosed_iInter` | an intersection of sup-closed sets is sup-closed |
| `SupClosed.image` | the image along a map that keeps $\sqcup$ is sup-closed |
| `SupClosed.prod` | a product of sup-closed sets is sup-closed |
| `supClosed_pi` | a product of a family of sup-closed sets is sup-closed |
| `SupClosed.finsetSup'_mem` | the supremum of a nonempty finite family in $s$ is in $s$ |
| `SupClosed.sSup_mem` | in a complete lattice, if $\bot \in s$, then $\sup t \in s$ for each finite $t \subseteq s$ |

The proof of `SupClosed.finsetSup'_mem` is an induction on the nonempty finset: a singleton gives $f(i) \in s$, and a step adds one element with the closure property. The hypothesis $\bot \in s$ in `SupClosed.sSup_mem` takes care of the empty set $t$, whose supremum is $\bot$.

A sup-closed set has one more use. `SemilatticeSup.toCompleteSemilatticeSup` builds a complete join-semilattice from a join-semilattice and a function `sSup` that gives a least upper bound to each sup-closed set. The reason is that the least upper bound of an arbitrary set $s$ is the least upper bound of the set of the finite suprema of elements of $s$, and that set is sup-closed.

#### The closures

The definition `supClosure` is a `ClosureOperator (Set α)`: `supClosure s` is the smallest sup-closed set that contains $s$. Its elements are the suprema of the nonempty finite subsets of $s$. The basic lemmas are `subset_supClosure`, `supClosed_supClosure` and `supClosure_min` (if $s \subseteq t$ and $t$ is sup-closed, then `supClosure s ⊆ t`), and `supClosure_eq_self` says that a sup-closed set is its own closure. The closure keeps the order data: `upperBounds_supClosure` says that $s$ and its closure have the same upper bounds, and so `isLUB_supClosure` says that they have the same least upper bound. `Set.Finite.supClosure` says that the closure of a finite set is finite. The dual `infClosure` has the dual lemmas.

The definition `latticeClosure` is the smallest sublattice that contains $s$. Its description is harder, because $\sqcup$ and $\sqcap$ alternate, and an element can need a long term. The induction principle `latticeClosure_sup_inf_induction` is the main tool. To prove a property $p$ of each element of `latticeClosure s`, it is enough to prove $p$ for the elements of $s$ and to show that $p$ goes from $a$ and $b$ to $a \sqcup b$ and to $a \sqcap b$. `latticeClosure_min` is the minimality.

In a distributive lattice the description becomes simple. Each element of the lattice closure is a finite supremum of finite infima of elements of $s$, because the distributive law moves each $\sqcap$ inside each $\sqcup$. So the closure of a finite set is finite, `Set.Finite.latticeClosure`, and the closure of a product is the product of the closures, `latticeClosure_prod`. Both lemmas need `DistribLattice`. Without distributivity, the free lattice on three generators is infinite, so the finite statement is false.

#### The bundled sublattices

The structure `Sublattice α` bundles a set with the two closure properties, `Sublattice.supClosed` and `Sublattice.infClosed`. It is a `SetLike` type, so `a ∈ L` and the coercion to `Set α` work as for subgroups, and `Sublattice.ext` proves equality from the elements. `Sublattice.ofIsSublattice` bundles a set with a proof of `IsSublattice`. The coercion of a sublattice to a type is a lattice, `Sublattice.instLatticeCoe`, with the operations of $\alpha$, by `Sublattice.coe_sup` and `Sublattice.coe_inf`. If $\alpha$ is distributive, so is each sublattice, `Sublattice.instDistribLatticeCoe`.

The sublattices of $\alpha$ form a complete lattice, `Sublattice.instCompleteLattice`, ordered by inclusion. The infimum is the intersection, `Sublattice.mem_inf` and `Sublattice.mem_sInf`. The top is the whole type, `Sublattice.coe_top`, and `Sublattice.topEquiv` identifies it with $\alpha$. The bottom is the empty set, `Sublattice.coe_bot` and `Sublattice.notMem_bot`, because a sublattice does not have to contain a bottom element of $\alpha$. This differs from subgroups, where the bottom is $\{1\}$.

A lattice homomorphism $f : \alpha \to \beta$, a `LatticeHom α β` from Section 4, moves sublattices in both directions. `Sublattice.map f L` is the image, with `Sublattice.mem_map`, and `Sublattice.comap f M` is the preimage, with `Sublattice.mem_comap`. The main fact is the Galois connection `Sublattice.gc_map_comap`, in the form of `Sublattice.map_le_iff_le_comap`: `map f L ≤ M` if and only if `L ≤ comap f M`. Both sides say that $f(a) \in M$ for each $a \in L$. From the Galois connection, `Sublattice.map_sup` says that the image keeps suprema of sublattices, and `Sublattice.map_inf_le` gives only an inclusion for infima, since the image of an intersection can be smaller than the intersection of the images.

The structure maps are `Sublattice.subtype`, the inclusion of $L$ in $\alpha$ as a lattice homomorphism, and `Sublattice.inclusion`, the inclusion of $L$ in $M$ for $L \le M$. The range of a lattice homomorphism is the sublattice `Sublattice.LatticeHom.range`. For products, `Sublattice.prod` gives the product of two sublattices, with the isomorphism `Sublattice.prodEquiv` to the product of the two lattices, and `Sublattice.pi` gives the product of a family.

#### Intervals as lattices

Each interval of a lattice is a sublattice. For $x, y \ge a$ the elements $x \sqcup y$ and $x \sqcap y$ are again $\ge a$, so `Set.Ici.instLatticeElem` makes `Set.Ici a` a lattice. In the same way `Set.Iic.instLatticeElem` and `Set.Icc.lattice` give lattice instances on `Set.Iic a` and `Set.Icc a b`. The interval `Set.Iic a` has the top element $a$, and a bottom element when $\alpha$ has one, `Set.Iic.instBoundedOrderElemOfOrderBot`. The interval `Set.Icc a b` is a bounded order only when it is not empty. The instance `Set.Icc.instBoundedOrderElemOfFactLe` takes the hypothesis $a \le b$ as an instance of `Fact (a ≤ b)`.

The complements in an interval are described with the operations of $\alpha$. In `Set.Iic a`, two elements are disjoint if their infimum is $\bot$, `Set.Iic.disjoint_iff`, and they are codisjoint if their supremum is $a$, `Set.Iic.codisjoint_iff`. So `Set.Iic.isCompl_iff` gives the condition $x \sqcap y = \bot$ and $x \sqcup y = a$. For a closed interval, `Set.Icc.isCompl_iff` gives
$$\operatorname{IsCompl} x\, y \iff x \sqcap y = a \wedge x \sqcup y = b.$$
The lemmas `Set.Iic.complementedLattice_iff` and `Set.Ici.complementedLattice_iff` turn the statement "each interval $(-\infty, a]$ is complemented" into a statement about relative complements in $\alpha$. These statements are used in the study of complemented modular lattices.

#### Lattice congruences

A structure `LatticeCon α` is an equivalence relation on $\alpha$, given by the projection `LatticeCon.toSetoid`, with two compatibility fields. `LatticeCon.inf` says that $x \sim y$ and $z \sim w$ give $x \sqcap z \sim y \sqcap w$, and `LatticeCon.sup` is the same for $\sqcup$. These are the conditions that make the set of the classes a lattice with the induced operations.

A useful criterion is `LatticeCon.r_inf_sup_iff`: $x \sim y$ if and only if $x \sqcap y \sim x \sqcup y$. Proof. If $x \sim y$, then $x \sqcap y \sim x \sqcap x = x$ and $x \sqcup y \sim x \sqcup x = x$, so the two are related. Conversely, if $x \sqcap y \sim x \sqcup y$, then
$$x = x \sqcap (x \sqcup y) \sim x \sqcap (x \sqcap y) = x \sqcap y,$$
by the compatibility with $\sqcap$ and the absorption law, and in the same way $y \sim x \sqcap y$. So $x \sim y$ by transitivity.

The constructor `LatticeCon.mk'` checks a congruence on comparable pairs only. Its hypotheses are:

1. the relation is reflexive;
2. $x \sim y$ if and only if $x \sqcap y \sim x \sqcup y$;
3. for $x \le y \le z$, $x \sim y$ and $y \sim z$ give $x \sim z$;
4. for $x \le y$ with $x \sim y$ and each $t$, $x \sqcap t \sim y \sqcap t$ and $x \sqcup t \sim y \sqcup t$.

The constructor proves symmetry, full transitivity and full compatibility from these four conditions. In examples, the conditions on comparable pairs are much easier to check. The kernel of a lattice homomorphism $f$, the relation $f(x) = f(y)$, is a congruence, `LatticeCon.ker`, with `LatticeCon.ker_r` as its unfolding lemma.

#### Common errors

1. The bottom of `Sublattice α` is the empty sublattice, not $\{\bot\}$. A proof that `⊥ ∈ L` for each `L : Sublattice α` cannot work, and `Sublattice.notMem_bot` shows it.
2. `IsSublattice s` is a condition on the operations of $\alpha$. A subset that is a lattice for the induced order, but with different suprema, is not a sublattice, and the instance `Sublattice.instLatticeCoe` only applies to the bundled form.
3. The bounded order on `Set.Icc a b` needs an instance of `Fact (a ≤ b)`. Without it, `⊤` and `⊥` do not elaborate on the interval, and a local `haveI : Fact (a ≤ b) := ⟨h⟩` fixes the error.

### Exercises

1. (A) Show that the set of the even natural numbers is sup-closed for the divisibility order on $\mathbb{N}$, in which $a \sqcup b$ is the least common multiple.
2. (A) Use `latticeClosure_sup_inf_induction` to prove that if each element of $s$ is below $a$, then each element of `latticeClosure s` is below $a$.
3. (B) Prove `LatticeCon.r_inf_sup_iff` from the fields `LatticeCon.inf` and `LatticeCon.sup` and the absorption laws.
4. (B) Show that the kernel of a lattice homomorphism is a congruence, and describe the congruence of the map from the lattice $\{0, 1, 2\}$ with the usual order onto $\{0, 1\}$ that sends $0$ to $0$ and $1$ and $2$ to $1$.
5. (B) Prove `Sublattice.map_le_iff_le_comap` from `Sublattice.mem_map` and `Sublattice.mem_comap`, and give an example where `Sublattice.map_inf_le` is a strict inclusion.
6. (C) In the lattice $M_3$ with atoms $a$, $b$ and $c$, compute `latticeClosure {a, b}` and `latticeClosure {a, b, c}`. Then show that in a distributive lattice the lattice closure of a set with $n$ elements has at most $2^{2^n}$ elements.

### Reference

<?reference?>
