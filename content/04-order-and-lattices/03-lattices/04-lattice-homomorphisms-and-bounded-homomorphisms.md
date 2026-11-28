---
title: Lattice homomorphisms and bounded homomorphisms
kind: api
modules:
  - Mathlib.Order.Hom.Lattice
  - Mathlib.Order.Hom.Bounded
  - Mathlib.Order.Hom.BoundedLattice
  - Mathlib.Order.Hom.WithTopBot
explains:
  E2: [SupHomClass.toOrderHomClass, OrderHomClass.toLatticeHomClass, orderEmbeddingOfInjective, Disjoint.map, IsCompl.map, "map_compl'", SupHom.instSemilatticeSup, LatticeHom.withTopWithBot]
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

## Lattice homomorphisms and bounded homomorphisms

### Overview

A monotone map between two lattices need not keep the lattice operations. The map from the subsets of $\{1, 2\}$ to $\{0, 1\}$ that sends a set to $1$ exactly when it contains both points is monotone, but it sends $\{1\} \cup \{2\}$ to $1$ and the two sets to $0$. A *lattice homomorphism* is a map $f$ with $f(a \sqcup b) = f(a) \sqcup f(b)$ and $f(a \sqcap b) = f(a) \sqcap f(b)$. A *bounded* lattice homomorphism also keeps $\top$ and $\bot$. These maps are the morphisms of the algebraic view of lattices from Section 1.

Mathlib has one bundled type for each useful set of operations: maps that keep $\sqcup$, maps that keep $\sqcap$, maps that keep $\top$, and their combinations. The four modules of this section define these types, the classes that go with them, the lemmas that move a map through an operation, and the extension of a map to `WithTop α` and `WithBot α`. The bundled order maps `α →o β`, `α ↪o β` and `α ≃o β` of Chapter 2 are the model: each type here has the same API of identity, composition, extensionality and coercion.

### The library around it

**The types and the classes.** Each kind of map is a structure with a field for the function and one field for each operation that it keeps. Each structure has a companion class, and the lemmas are stated for the class. So one lemma serves the structure, the stronger structures, and the order isomorphisms. The table lists the types of `Mathlib.Order.Hom.Lattice`, `Mathlib.Order.Hom.Bounded` and `Mathlib.Order.Hom.BoundedLattice`.

| Lean name | Statement |
|---|---|
| `SupHom α β` | maps with $f(a \sqcup b) = f(a) \sqcup f(b)$, class `SupHomClass` |
| `InfHom α β` | maps with $f(a \sqcap b) = f(a) \sqcap f(b)$, class `InfHomClass` |
| `LatticeHom α β` | maps that keep $\sqcup$ and $\sqcap$, class `LatticeHomClass` |
| `TopHom α β` | maps with $f(\top) = \top$, class `TopHomClass` |
| `BotHom α β` | maps with $f(\bot) = \bot$, class `BotHomClass` |
| `BoundedOrderHom α β` | monotone maps that keep $\top$ and $\bot$, class `BoundedOrderHomClass` |
| `SupBotHom α β` | maps that keep $\sqcup$ and $\bot$, class `SupBotHomClass` |
| `InfTopHom α β` | maps that keep $\sqcap$ and $\top$, class `InfTopHomClass` |
| `BoundedLatticeHom α β` | maps that keep $\sqcup$, $\sqcap$, $\top$ and $\bot$, class `BoundedLatticeHomClass` |

The axioms of the classes are `SupHomClass.map_sup`, `InfHomClass.map_inf`, `TopHomClass.map_top` and `BotHomClass.map_bot`. Mathlib exports them, so a proof can write them without the class prefix, and `simp` uses them for each type of map at once. The forgetful maps have the names of the target type: `LatticeHom.toSupHom`, `LatticeHom.toInfHom`, `BoundedLatticeHom.toLatticeHom`, `BoundedLatticeHom.toSupBotHom`, `BoundedLatticeHom.toBoundedOrderHom`, `BoundedOrderHom.toTopHom` and `BoundedOrderHom.toBotHom`. Their coercions to functions are equal by `simp` lemmas such as `LatticeHom.coe_toSupHom`.

**The common API.** Each type `T` has `T.id`, `T.comp`, `T.ext`, `T.copy`, `T.coe_comp`, `T.comp_apply`, `T.id_comp`, `T.comp_id`, `T.comp_assoc`, and the two cancellation lemmas: `LatticeHom.cancel_right` says that $g_1 \circ f = g_2 \circ f$ if and only if $g_1 = g_2$ when $f$ is surjective, and `LatticeHom.cancel_left` is the same with an injective $g$ on the left. The function `T.copy` replaces the underlying function by an equal function with better definitional properties, and `LatticeHom.copy` is the standard example.

**Order maps and lattice maps.** A map that keeps $\sqcup$ is monotone. This is the instance `SupHomClass.toOrderHomClass`. *Proof.* If $a \le b$ then $a \sqcup b = b$, so $f(a) \sqcup f(b) = f(a \sqcup b) = f(b)$, and this says $f(a) \le f(b)$. $\square$ The converse fails in general, as the overview shows, but it holds on a linear order. The instance `OrderHomClass.toLatticeHomClass` makes each monotone map from a linear order to a lattice a lattice homomorphism, and `OrderHomClass.toLatticeHom` gives the bundled map. *Proof.* Let $a \le b$, the other case is symmetric. Then $a \sqcup b = b$, and $f(a) \le f(b)$ gives $f(a) \sqcup f(b) = f(b)$. So $f(a \sqcup b) = f(a) \sqcup f(b)$. The same argument works for $\sqcap$. $\square$ An order isomorphism keeps every operation that the order defines, so `OrderIsoClass.toLatticeHomClass` and `OrderIsoClass.toBoundedLatticeHomClass` are instances, and `map_eq_top_iff` and `map_eq_bot_iff` say that an order isomorphism sends only $\top$ to $\top$ and only $\bot$ to $\bot$.

For the other direction, an injective map that keeps $\sqcap$ is an order embedding. The definition `orderEmbeddingOfInjective` bundles it. *Proof.* In a semilattice $a \le b$ holds if and only if $a \sqcap b = a$. Apply $f$: $f(a \sqcap b) = f(a)$ is $f(a) \sqcap f(b) = f(a)$, and injectivity gives back $a \sqcap b = a$. $\square$

**Examples.** The projections `LatticeHom.fst` and `LatticeHom.snd` from $\alpha \times \beta$, and the evaluation `Pi.evalLatticeHom` at an index of a product $\prod_i \alpha_i$, are lattice homomorphisms. The inclusion of a subset that is closed under $\sqcup$ and $\sqcap$ is `LatticeHom.subtypeVal`, and `SupHom.subtypeVal`, `SupBotHom.subtypeVal` and `BoundedLatticeHom.subtypeVal` are the forms for the other kinds of closure. For a function $f : X \to Y$ the preimage keeps unions and intersections by `Set.preimage_union` and `Set.preimage_inter`, while the image keeps unions by `Set.image_union` but only satisfies `Set.image_inter_subset` for intersections. So the image is a sup homomorphism and in general not a lattice homomorphism.

**Order and lattice structure on the maps.** Two maps of the same type are compared pointwise. The pointwise supremum of two sup homomorphisms is a sup homomorphism, so `SupHom.instSemilatticeSup` makes `SupHom α β` a semilattice, with `SupHom.sup_apply` as the rule $(f \sqcup g)(a) = f(a) \sqcup g(a)$. *Proof.* $(f \sqcup g)(a \sqcup b) = f(a) \sqcup f(b) \sqcup g(a) \sqcup g(b) = (f(a) \sqcup g(a)) \sqcup (f(b) \sqcup g(b))$, by associativity and commutativity of $\sqcup$ in $\beta$. $\square$ The constant map `SupHom.const` keeps $\sqcup$ because $b \sqcup b = b$, and the constant maps at $\bot$ and $\top$ make `SupHom α β` a bounded order when $\beta$ is bounded, by `SupHom.instBoundedOrder`. The dual statements hold for `InfHom`, with `InfHom.instSemilatticeInf`. The same proof does not work for `LatticeHom`, because the pointwise supremum of two lattice homomorphisms need not keep $\sqcap$, and Mathlib gives `LatticeHom α β` no order structure. The maps that keep only $\top$ form a lattice, `TopHom.instLattice`, and a distributive lattice when $\beta$ is distributive, `TopHom.instDistribLattice`.

**Duality.** Each type has a `dual` equivalence that reverses both orders. `SupHom.dual` is an equivalence between `SupHom α β` and `InfHom αᵒᵈ βᵒᵈ`, `TopHom.dual` sends top homomorphisms to bottom homomorphisms, and `LatticeHom.dual` and `BoundedLatticeHom.dual` keep their type. Many files prove a statement for one side and deduce the other with these equivalences.

**Complements and disjointness.** A map that keeps $\sqcap$ and $\bot$ keeps disjointness: `Disjoint.map` says that $a \sqcap b = \bot$ gives $f(a) \sqcap f(b) = \bot$. The dual is `Codisjoint.map`, and together they give `IsCompl.map` for a bounded lattice homomorphism. Since a complement in a distributive lattice is unique, a bounded lattice homomorphism between Boolean algebras keeps the complement. This is `map_compl'`. *Proof.* `IsCompl.map` turns the pair $a, a^c$ into the complementary pair $f(a), f(a^c)$. The complement of $f(a)$ is unique, so $f(a^c) = f(a)^c$ by `IsCompl.compl_eq`. $\square$ The consequences `map_sdiff'` and `map_symmDiff'` follow, because $a \setminus b = a \sqcap b^c$ in a Boolean algebra.

**Extension to `WithTop` and `WithBot`.** The module `Mathlib.Order.Hom.WithTopBot` extends maps to the types with a new top or a new bottom of Volume 2. The inclusion is `WithTop.coeOrderHom`, an order embedding. A monotone map extends by `OrderHom.withTopMap`, an embedding by `OrderEmbedding.withTopMap` and an isomorphism by `OrderIso.withTopCongr`. Each of them sends the new top to the new top, and its function is `WithTop.map` of the old function. For lattice maps the family has two forms. `LatticeHom.withTop` sends `WithTop α` to `WithTop β`, with `LatticeHom.coe_withTop` as its formula. The primed `LatticeHom.withTop'` sends `WithTop α` to $\beta$ itself when $\beta$ already has a top, and sends the new top to $\top$. The map `SupHom.withBot` is a `SupBotHom`, because it sends the new bottom to the new bottom. The two steps together give `LatticeHom.withTopWithBot`, a bounded lattice homomorphism from `WithTop (WithBot α)` to `WithTop (WithBot β)`. *Proof sketch.* A lattice homomorphism extended by $\bot \mapsto \bot$ keeps $\sqcup$, because $\bot$ is neutral for $\sqcup$ on both sides, and it keeps $\sqcap$, because $\bot$ absorbs $\sqcap$ on both sides. The same holds for the new top with the roles exchanged, and the extension keeps the two new bounds by construction. $\square$ The `WithBot` names are the same with `Bot` in place of `Top`, for example `OrderIso.withBotCongr` and `LatticeHom.withBot'`. Two order isomorphisms close the module: `WithTop.toDualBotEquiv` identifies `WithTop αᵒᵈ` with the dual of `WithBot α`, and `WithTop.subtypeOrderIso` identifies a type with a top with `WithTop` of the type of its elements other than $\top$.

#### Common errors

1. A `LatticeHom` between two Boolean algebras does not keep the complement in general: it can send $\bot$ to an element other than $\bot$. Use `BoundedLatticeHom` before `map_compl'`, or `HeytingHom` in a Heyting algebra.
2. `LatticeHom α β` has no lattice structure, and not even an order. A sum or a supremum of maps only makes sense for `SupHom`, `InfHom` and the `TopHom` and `BotHom` families.
3. The equality of two bundled maps is not the equality of their functions. Prove it with the extensionality lemma, for example `LatticeHom.ext`, and use the `copy` construction when a definition needs a specific function.

### Exercises

1. (A) Show that $x \mapsto x^3$ on $\mathbb{R}$ is a lattice homomorphism, and give its bundled form with `OrderHomClass.toLatticeHom`.
2. (A) Let $X$ be a set and $x \in X$. Show that $s \mapsto (x \in s)$ is a bounded lattice homomorphism from the subsets of $X$ to the propositions.
3. (B) Give two lattice homomorphisms $f, g : \{0, 1\}^2 \to \{0, 1\}^2$ whose pointwise supremum does not keep $\sqcap$. Explain why this shows that `LatticeHom α β` cannot be a semilattice with the pointwise order.
4. (B) Show that a surjective lattice homomorphism that keeps $\bot$ sends each atom to an atom or to $\bot$. Give an example where an atom goes to $\bot$.
5. (B) Prove `Disjoint.map` from `InfHomClass.map_inf` and `BotHomClass.map_bot`, and use `LatticeHom.dual` to deduce a form of `Codisjoint.map` for lattice homomorphisms that keep $\top$.
6. (C) Let $f$ be a bounded lattice homomorphism from a Boolean algebra $A$ to the two-element Boolean algebra. Show that the set of $a$ with $f(a) = \top$ is an ultrafilter of $A$, and that each ultrafilter arises in this way.

### Reference

<?reference?>
