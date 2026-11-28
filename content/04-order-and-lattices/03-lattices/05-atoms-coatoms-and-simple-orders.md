---
title: Atoms, coatoms and simple orders
kind: api
modules:
  - Mathlib.Order.Atoms
  - Mathlib.Order.Atoms.Finite
explains:
  E2: [bot_covBy_iff, Set.isAtom_iff, Pi.isAtom_iff, Finite.to_isAtomic, isSimpleOrder_iff_isAtom_top, IsCompl.isAtom_iff_isCoatom, CompleteAtomicBooleanAlgebra.toSetOfIsAtom]
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

## Atoms, coatoms and simple orders

### Overview

An atom of an order with a least element $\bot$ is an element $a \ne \bot$ with nothing strictly between $\bot$ and $a$. In the lattice of subsets of a set the atoms are the singletons. In the lattice of subgroups of a group the atoms are the subgroups of prime order, and in the lattice of subspaces of a vector space they are the lines. A coatom is the dual notion: an element $a \ne \top$ with nothing strictly between $a$ and $\top$. The maximal ideals of a ring are the coatoms of its lattice of ideals.

The two files of this section define atoms and coatoms, the classes of orders in which there are enough atoms (atomic, atomistic and strongly atomic orders), and the simple orders, which have exactly the two elements $\bot$ and $\top$. They use the bounded orders and the Boolean algebras of the earlier sections of this chapter, the covering relation $a \lessdot b$ of Chapter 1, and the order isomorphisms of Chapter 2. A few results state facts about suprema in a complete lattice or a frame, and these use the notation of Chapter 4.

### The library around it

**Atoms and coatoms.** The predicate `IsAtom a` needs a preorder with `OrderBot`, and it is the conjunction $a \ne \bot$ and $\forall b,\ b < a \to b = \bot$. The predicate `IsCoatom a` is its dual for `OrderTop`. Each lemma on atoms has a twin on coatoms, made by the `to_dual` attribute: the name changes *Atom* to *Coatom*, *bot* to *top*, *Iic* to *Ici*, *disjoint* to *codisjoint*, and the order turns. The lemmas `isAtom_dual_iff_isCoatom` and `isCoatom_dual_iff_isAtom` connect the two through the order dual. In a partial order an atom $a$ satisfies $x < a \iff x = \bot$ (`IsAtom.lt_iff`), $x \le a \iff x = \bot \lor x = a$ (`IsAtom.le_iff`) and $\operatorname{Iic} a = \{\bot, a\}$ (`IsAtom.Iic_eq`). In terms of the covering relation, an atom is exactly an element that covers $\bot$.

$$\bot \lessdot a \iff \operatorname{IsAtom} a \qquad (\texttt{bot\_covBy\_iff}).$$

*Proof.* The relation $\bot \lessdot a$ says $\bot < a$ and no $c$ satisfies $\bot < c < a$. The first part is $a \ne \bot$. The second part says that each $c < a$ is not $> \bot$, that is $c = \bot$. These are the two parts of `IsAtom a`. $\square$

In a meet-semilattice with $\bot$, two distinct atoms are disjoint (`IsAtom.disjoint_of_ne`), and for an atom $a$ the statement $a \not\le b$ is the same as $a \sqcap b = \bot$ (`IsAtom.not_le_iff_disjoint`). In a frame, an atom below a supremum is below one of the terms: `IsAtom.le_iSup` and `IsAtom.le_sSup`. The lemma `covBy_iff_atom_Ici` reduces a covering $a \lessdot b$ to an atom of the interval `Set.Ici a`, and `IsAtom.Iic` and `IsAtom.of_isAtom_coe_Iic` move atoms in and out of `Set.Iic x`.

**Atoms of the standard lattices.** Several lemmas compute the atoms of a concrete lattice.

| Lean name | Statement |
| --- | --- |
| `Set.isAtom_iff` | $s$ is an atom of `Set α` iff $s = \{x\}$ for some $x$ |
| `Set.isCoatom_iff` | $s$ is a coatom of `Set α` iff $s = \{x\}^c$ for some $x$ |
| `Prop.isAtom_iff` | a proposition $p$ is an atom iff $p$ holds |
| `Pi.isAtom_iff` | $f$ is an atom of $\prod_i \pi_i$ iff one $f_i$ is an atom and $f_j = \bot$ for $j \ne i$ |
| `isAtom_compl` | in a Boolean algebra, $a^c$ is an atom iff $a$ is a coatom |
| `SetLike.isAtom_iff` | the atoms of a lattice of subobjects, in terms of elements |

*Proof of `Set.isAtom_iff`.* A singleton $\{x\}$ is nonempty, and a proper subset of it is empty, so it is an atom. Conversely, let $s$ be an atom. Then $s \ne \emptyset$, so $s$ has an element $x$. The set $\{x\}$ is a nonempty subset of $s$, and if it were a proper subset it would be $\emptyset$. So $\{x\} = s$. $\square$

*Proof of `Pi.isAtom_iff`.* The order on functions is pointwise, and $\bot$ is the constant function $\bot$. If $f$ has two indices $i \ne j$ with $f_i \ne \bot$ and $f_j \ne \bot$, then the function equal to $f_i$ at $i$ and $\bot$ elsewhere is strictly between $\bot$ and $f$. So an atom has exactly one nonzero coordinate $i$, and an element strictly below $f_i$ gives an element strictly below $f$, so $f_i$ is an atom. The converse is the same argument read backwards. $\square$

The construction in the other direction is `Pi.isAtom_single`: if $a$ is an atom of $\pi_i$, then `Function.update ⊥ i a` is an atom of the product. Atoms move along maps: `OrderIso.isAtom_iff` for an order isomorphism, `OrderEmbedding.isAtom_of_map_bot_of_image` for an embedding $f$ with $f(\bot) = \bot$ (if $f(b)$ is an atom, then $b$ is an atom), and `GaloisInsertion.isAtom_iff` for a Galois insertion with $u(\bot) = \bot$.

**Atomic and atomistic orders.** The class `IsAtomic α` says that each $b \ne \bot$ is above an atom, and `IsAtomic.exists_atom` gives an atom in a nontrivial atomic order. The class `IsAtomistic α` is stronger: each $b$ is the least upper bound of a set of atoms. The instance `IsAtomistic.instIsAtomic` gives the implication. In an atomistic order $b$ is the least upper bound of all the atoms below it (`isLUB_atoms_le`), and in a complete lattice this reads $\operatorname{sSup}\{a \mid \operatorname{IsAtom} a \land a \le b\} = b$ (`sSup_atoms_le_eq`) and $\operatorname{sSup}\{a \mid \operatorname{IsAtom} a\} = \top$ (`sSup_atoms_eq_top`). So an atomistic order is determined by its atoms: $a \le b$ holds iff each atom below $a$ is below $b$ (`le_iff_atom_le_imp`). In a Boolean algebra it is enough to be atomic for the same test, and this is `BooleanAlgebra.le_iff_atom_le_imp`.

A well-founded order with $\bot$ is atomic (`isAtomic_of_orderBot_wellFounded_lt`). Atomicity is local: `isAtomic_iff_forall_isAtomic_Iic` says that $\alpha$ is atomic iff each interval $\operatorname{Iic} x$ is atomic. The class `IsStronglyAtomic α` asks more: for each $a < b$ there is $x$ with $a \lessdot x \le b$ (`exists_covBy_le_of_lt`). A strongly atomic order with $\bot$ is atomic (`IsStronglyAtomic.isAtomic`). Each order with a well-founded $<$ and each `SuccOrder` is strongly atomic (`SuccOrder.toIsStronglyAtomic`), and the property passes to order-connected subsets (`Set.OrdConnected.isStronglyAtomic`). An upper modular atomistic lattice is strongly atomic (`Lattice.isStronglyAtomic`).

**Complemented modular lattices.** In a bounded modular lattice, complements exchange atoms and coatoms.

$$\operatorname{IsCompl} a\, b \implies (\operatorname{IsAtom} a \iff \operatorname{IsCoatom} b) \qquad (\texttt{IsCompl.isAtom\_iff\_isCoatom}).$$

*Proof sketch.* Modularity gives an order isomorphism between the intervals $[\bot, a]$ and $[b, \top]$, the map $x \mapsto x \sqcup b$ with inverse $y \mapsto y \sqcap a$. An element $a$ is an atom iff $[\bot, a]$ has exactly two elements, and $b$ is a coatom iff $[b, \top]$ has exactly two elements. The isomorphism matches the two conditions. $\square$

As a consequence a complemented modular lattice is atomic iff it is coatomic (`isAtomic_iff_isCoatomic`), and then it is also strongly atomic (`ComplementedLattice.isStronglyAtomic`). The lattice of subspaces of a vector space is an example.

**Complete atomic Boolean algebras.** A complete Boolean algebra that is atomic is a `CompleteAtomicBooleanAlgebra`, through the definition `CompleteBooleanAlgebra.toCompleteAtomicBooleanAlgebra`. Such an algebra is a power set:

$$\alpha \simeq_o \mathcal{P}(\{a : \alpha \mid \operatorname{IsAtom} a\}) \qquad (\texttt{CompleteAtomicBooleanAlgebra.toSetOfIsAtom}).$$

*Proof sketch.* The map sends $x$ to the set of the atoms below $x$. It is monotone. It is injective and reflects the order because the algebra is atomistic, so $x \le y$ iff each atom below $x$ is below $y$. It is surjective: for a set $S$ of atoms, the supremum $\bigvee S$ has exactly the atoms of $S$ below it, because an atom below a supremum is below a term (the algebra is a frame), and below a term means equal to it. $\square$

**Simple orders.** The class `IsSimpleOrder α` asks a bounded order to be nontrivial with each element equal to $\bot$ or $\top$. So $\alpha$ has exactly the two elements $\bot \ne \top$. A bounded partial order is simple iff its top is an atom:

$$\operatorname{IsSimpleOrder} \alpha \iff \operatorname{IsAtom} \top \qquad (\texttt{isSimpleOrder\_iff\_isAtom\_top}).$$

*Proof.* If $\alpha$ is simple, then $\top \ne \bot$, and each $b < \top$ is not $\top$, so it is $\bot$. Conversely, if $\top$ is an atom, then $\bot \ne \top$, so $\alpha$ is nontrivial, and each $b$ satisfies $b = \top$ or $b < \top$, and the second case gives $b = \bot$. $\square$

In the same way `Set.isSimpleOrder_Iic_iff_isAtom` says that $a$ is an atom iff the interval $\operatorname{Iic} a$ is a simple order. A simple order is unique up to isomorphism: `IsSimpleOrder.orderIsoBool` is an order isomorphism with `Bool`, and `IsSimpleOrder.equivBool` is the underlying bijection. Both need `DecidableEq α`. A simple order also carries the definitions `IsSimpleOrder.linearOrder`, `IsSimpleOrder.booleanAlgebra` and `IsSimpleOrder.completeBooleanAlgebra`, which are not instances (the first two need `DecidableEq α`), and the instances `IsSimpleOrder.instIsAtomic` and `IsSimpleOrder.instIsAtomistic`. In a simple order $\top$ is the only atom (`isAtom_iff_eq_top`) and $\bot \lessdot \top$ (`bot_covBy_top`). The instance `Prop.instIsSimpleOrderProp` makes `Prop` simple. In algebra, a simple module is defined through this class on the lattice of its submodules.

**Finite orders.** The file `Mathlib.Order.Atoms.Finite` treats the finite case.

$$\alpha \text{ finite with } \bot \implies \alpha \text{ atomic} \qquad (\texttt{Finite.to\_isAtomic}).$$

*Proof.* A finite partial order is well founded, so the result of `isAtomic_of_orderBot_wellFounded_lt` applies. Directly: for $b \ne \bot$ the set $\{x \mid \bot < x \le b\}$ is finite and contains $b$, so it has a minimal element $a$. An element $c < a$ with $c \ne \bot$ would be in the set and smaller than $a$, so no such $c$ exists, and $a$ is an atom. $\square$

The dual is `Finite.to_isCoatomic`. A locally finite order is strongly atomic and strongly coatomic, by the instances `instIsStronglyAtomic` and `instIsStronglyCoatomic`. For a simple order, `Fintype.IsSimpleOrder.univ` says that the universe is $\{\top, \bot\}$ and `Fintype.IsSimpleOrder.card` says that it has two elements, and `Bool.instIsSimpleOrder` makes `Bool` simple. The lemma `exists_covby_infinite_Ici_of_infinite_Ici` is a form of the lemma of König: in a strongly atomic order, if $\operatorname{Ici} a$ is infinite and $a$ has only finitely many covers, then one cover $b$ of $a$ has $\operatorname{Ici} b$ infinite.

#### Common errors

1. `IsAtom` needs only `OrderBot`, but most of its lemmas need a partial order. In a preorder an element equivalent to $\bot$ is not equal to it, and lemmas such as `IsAtom.lt_iff` are not available.
2. `IsAtomic` and `IsAtomistic` are different classes. An atomic order can have an element that is not a supremum of atoms; the instance only goes from atomistic to atomic. In a Boolean algebra the two agree for the order test, but the lemma to use is then `BooleanAlgebra.le_iff_atom_le_imp`, not `le_iff_atom_le_imp`.
3. The Boolean algebra structure and the linear order of a simple order are definitions, not instances, and they need `DecidableEq α`. Use them with `letI` or through `IsSimpleOrder.orderIsoBool`.

### Exercises

1. (A) Prove that in `Set α` the coatoms are the complements of the singletons, from `Set.isAtom_iff` and `isAtom_compl`.
2. (A) Find the atoms and the coatoms of the lattice of the divisors of $60$ with the order of divisibility.
3. (A) Prove that an element covered by an atom of a partial order with $\bot$ is $\bot$, and state the dual result for coatoms.
4. (B) Prove that the order of the real numbers in $[0, 1]$ is bounded but not atomic, and that the lattice of subsets of $\mathbb{N}$ is atomistic.
5. (B) Prove that the chain $\bot < a < \top$ is atomic but not atomistic, and that each complete atomic Boolean algebra is atomistic.
6. (C) Prove `IsCompl.isAtom_iff_isCoatom` in full, with the order isomorphism between $[\bot, a]$ and $[b, \top]$ in a modular lattice.

### Reference

<?reference?>
