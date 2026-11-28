---
title: Permutation representations, faithful and pretransitive actions, and equidecompositions
kind: api
modules:
  - Mathlib.Algebra.Group.Action.Basic
  - Mathlib.Algebra.Group.Action.End
  - Mathlib.Algebra.Group.Action.Hom
  - Mathlib.Algebra.Group.Action.Faithful
  - Mathlib.Algebra.Group.Action.Pretransitive
  - Mathlib.Algebra.Group.Action.Equidecomp
explains:
  E2: [MulAction.toPerm, smul_left_cancel_iff, MulAction.toEndHom, MulAction.ofEndHom, MulAction.compHom, monoidHomEquivMulActionIsScalarTower, faithfulSMul_iff, faithfulSMul_iff_injective_smul_one, MulAction.IsPretransitive.of_orbit, Equidecomp.IsDecompOn.comp]
  E1: auto
families: []
requires: [V01, V05.C01, V05.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Permutation representations, faithful and pretransitive actions, and equidecompositions

### Overview

An action of a group $G$ on a set $\alpha$ is the same thing as a homomorphism from $G$ to the group of permutations of $\alpha$. An action of a monoid $M$ is the same thing as a homomorphism from $M$ to the monoid of all maps $\alpha \to \alpha$. These two translations are the base of the theory of actions, and this section describes the modules that hold them. The same modules define two properties of an action. The action is faithful when distinct elements act by distinct maps, and it is pretransitive when it has at most one orbit.

The modules split the work as follows. `Mathlib.Algebra.Group.Action.Basic` shows that each element of a group acts by a bijection and gives the lemmas for the cancellation of a scalar. `Mathlib.Algebra.Group.Action.End` gives the homomorphisms into the endomorphism monoid and into the permutation group, and the converse constructions. `Mathlib.Algebra.Group.Action.Hom` pulls an action back along a homomorphism of monoids. `Mathlib.Algebra.Group.Action.Faithful` and `Mathlib.Algebra.Group.Action.Pretransitive` define the two classes. The last module, `Mathlib.Algebra.Group.Action.Equidecomp`, defines equidecompositions: bijections between two sets that move each point by one of finitely many elements of the group.

The section uses the actions of Section 1 of this chapter and the homomorphisms of Chapter 2. The orbit-stabilizer theorem and the theorem of Cayley in Section 1 use the results here.

### The library around it

#### Each element acts by a bijection

Let $G$ be a group that acts on $\alpha$. The map $x \mapsto g \cdot x$ has the inverse $x \mapsto g^{-1} \cdot x$, because $g^{-1} \cdot (g \cdot x) = (g^{-1} g) \cdot x = 1 \cdot x = x$, and the same calculation holds in the other order. The library records this as `MulAction.injective`, `MulAction.surjective` and `MulAction.bijective`. The permutation itself is `MulAction.toPerm g`, with `MulAction.toPerm_apply` and `MulAction.toPerm_symm_apply` for the two directions.

Cancellation of a scalar follows. The lemma `smul_left_cancel_iff` states $g \cdot x = g \cdot y \iff x = y$, and `smul_eq_iff_eq_inv_smul` states $g \cdot x = y \iff x = g^{-1} \cdot y$. For a monoid, the same results hold for one element that has an inverse: `IsUnit.smul_left_cancel` and `IsUnit.smul_bijective` take a unit, and `smul_invOf_smul` and `invOf_smul_eq_iff` take an element with an `Invertible` instance.

The module also treats an action on a monoid that respects the multiplication, a `MulDistribMulAction`. Then each element acts by a monoid endomorphism, `MulDistribMulAction.toMonoidHom`, and the map $M \to \operatorname{End}(A)$ is the homomorphism `MulDistribMulAction.toMonoidEnd`. The lemmas `smul_pow'`, `smul_inv'` and `smul_div'` say that the action commutes with powers, inverses and division. A group that acts on $A$ also acts on the functions $A \to B$ by $(g \cdot F)(a) = F(g^{-1} \cdot a)$. This is `arrowAction`, and `arrowAction_smul` computes it. The inverse is necessary: without it the formula reverses the order of a product.

#### Actions as homomorphisms

The module `Mathlib.Algebra.Group.Action.End` states the translation in both directions. The monoid `Function.End α` is the monoid of all maps $\alpha \to \alpha$ under composition, with `Function.End.mul_def` as $f g = f \circ g$.

**Proposition.** The actions of a monoid $M$ on $\alpha$ correspond to the monoid homomorphisms $M \to \operatorname{End}(\alpha)$.

*Proof.* An action gives $\rho(m)(x) = m \cdot x$. Then $\rho(1) = \mathrm{id}$ because $1 \cdot x = x$, and $\rho(m n) = \rho(m) \circ \rho(n)$ because $(m n) \cdot x = m \cdot (n \cdot x)$. Conversely a homomorphism $\rho$ gives $m \cdot x = \rho(m)(x)$, and the two axioms of an action are the two properties of $\rho$. The two constructions are inverse to each other. $\square$

The two directions are `MulAction.toEndHom` and `MulAction.ofEndHom`. The monoid `Function.End α` itself acts on $\alpha$ by `Function.End.applyMulAction`, and this action is faithful. For a group the target is the permutation group: `MulAction.toPermHom G α : G →* Equiv.Perm α` sends $g$ to `MulAction.toPerm g`. The lemma `MulAction.toPerm_injective` states that this homomorphism is injective when the action is faithful. The same pattern holds for automorphisms. A group that acts on a monoid by a `MulDistribMulAction` gives `MulDistribMulAction.toMulAut : G →* MulAut M`, and `mulAutArrow` is the version for the action on functions. The permutation group, the automorphism group and the endomorphism monoid act on the base type by evaluation: `Equiv.Perm.applyMulAction`, `MulAut.applyMulAction` and `Function.End.applyMulAction`, with the lemmas `Equiv.Perm.smul_def` and `MulAut.smul_def`. The action of `Equiv.Perm α` is faithful and pretransitive, by `Equiv.Perm.applyFaithfulSMul` and `Equiv.Perm.instIsPretransitive`.

#### Change of the acting monoid

The module `Mathlib.Algebra.Group.Action.Hom` pulls back. If $f : N \to M$ is a monoid homomorphism and $M$ acts on $\alpha$, then $n \cdot x = f(n) \cdot x$ is an action of $N$. This is `MulAction.compHom`, with `MulAction.compHom_smul_def`. In terms of the proposition above it is the composite $N \to M \to \operatorname{End}(\alpha)$. A surjective $f$ keeps transitivity, by `MulAction.isPretransitive_compHom`. In the other direction, `Function.Surjective.mulActionLeft` pushes an action forward along a surjective homomorphism, when $f(c) \cdot x = c \cdot x$ defines the new action.

A monoid homomorphism $f : M \to N$ makes $M$ act on $N$ by $m \cdot n = f(m) n$. This action satisfies `IsScalarTower M N N`: $(m \cdot n) n' = m \cdot (n n')$. Conversely, an action with this property is determined by the elements $m \cdot 1$, since $m \cdot n = m \cdot (1 \cdot n) = (m \cdot 1) n$. The map $m \mapsto m \cdot 1$ is the homomorphism `MonoidHom.smulOneHom`. The equivalence `monoidHomEquivMulActionIsScalarTower` states the correspondence between the homomorphisms $M \to N$ and these actions.

#### Faithful actions

The class `FaithfulSMul M α` states that $m_1 \cdot x = m_2 \cdot x$ for all $x$ implies $m_1 = m_2$. In other words the map $M \to \operatorname{End}(\alpha)$ is injective. For a group it is enough to test one element against the identity: `faithfulSMul_iff` states that the action is faithful if and only if each $g$ that fixes all points is $1$. The proof applies the condition to $g_1^{-1} g_2$. The basic instances are the action of a monoid on itself, `instFaithfulSMul`, and the action of a cancellative monoid on itself on the right. A subsingleton monoid acts faithfully on each type, by `instFaithfulSMulOfSubsingleton`.

When $R$ acts on a monoid $A$ with `IsScalarTower R A A`, faithfulness is a statement about one element. Since $r \cdot a = (r \cdot 1) a$, the action is determined by the elements $r \cdot 1$. So `faithfulSMul_iff_injective_smul_one` states that the action is faithful if and only if $r \mapsto r \cdot 1$ is injective. The same argument gives `FaithfulSMul.tower_bot`: if $R$ acts faithfully on $T$ through a tower $R$, $S$, $T$, then $R$ acts faithfully on $S$.

#### Pretransitive actions

The class `MulAction.IsPretransitive M α` states that for each $x$ and $y$ some $m$ has $m \cdot x = y$. The field is `MulAction.IsPretransitive.exists_smul_eq`, and `MulAction.exists_smul_eq` is the form with an explicit $M$. The lemma `MulAction.isPretransitive_iff` unfolds the class, and `MulAction.surjective_smul` states that $m \mapsto m \cdot x$ is surjective for each $x$. The name says "pretransitive" because the empty set has the property: a transitive action also needs a nonempty set.

For a group it is enough to reach each point from one point $x_0$. If $g \cdot x_0 = x$ and $h \cdot x_0 = y$, then $(h g^{-1}) \cdot x = y$. This is `MulAction.IsPretransitive.of_orbit`. A group acts pretransitively on itself on the left and on the right, by `MulAction.Regular.isPretransitive` and `MulAction.Regular.isPretransitive_mulOpposite`. The lemma `MulAction.IsPretransitive.of_smul_eq` moves the property to a second acting type that contains the first in the sense $f(c) \cdot x = c \cdot x$, and `MulAction.IsPretransitive.of_isScalarTower` is the case of a tower.

#### Equidecompositions

Let $G$ act on $X$, and let $A$ and $B$ be subsets of $X$. Classically, $A$ and $B$ are equidecomposable when $A$ has a partition into finitely many pieces, and some elements $g_1, \dots, g_n$ of $G$ move these pieces to a partition of $B$. The library uses an equivalent form. A map $f : X \to X$ is a decomposition on $A$ with witness $S$, a finite subset of $G$, when $f(a) \in S \cdot a$ for each $a \in A$. This is `Equidecomp.IsDecompOn f A S`. An equidecomposition is a partial bijection with source $A$ and target $B$ that is a decomposition on $A$ for some finite $S$. This is the structure `Equidecomp X G`, with `Equidecomp.witness` for the chosen set $S$.

**Proposition.** Let $f$ be a decomposition on $A$ with witness $S$, let $g$ be a decomposition on $B$ with witness $T$, and let $f$ map $A$ into $B$. Then $g \circ f$ is a decomposition on $A$ with witness $T S$.

*Proof.* Let $a \in A$. Then $f(a) = s \cdot a$ for some $s \in S$, and $f(a) \in B$. So $g(f(a)) = t \cdot f(a) = t \cdot (s \cdot a) = (t s) \cdot a$ for some $t \in T$, and $t s \in T S$. $\square$

The library form is `Equidecomp.IsDecompOn.comp`. It gives the composite `Equidecomp.trans`, and `Equidecomp.refl` is the identity. For a group the inverse partial bijection is again an equidecomposition, with witness $S^{-1}$: this is `Equidecomp.IsDecompOn.of_leftInvOn` and `Equidecomp.symm`. The lemmas `Equidecomp.symm_symm` and `Equidecomp.left_inv` are the usual identities. The restriction `Equidecomp.restr` to a subset is again an equidecomposition, with `Equidecomp.restr_source` and `Equidecomp.restr_target`. So equidecomposability is an equivalence relation on the subsets of $X$. This notion is the start of the paradox of Banach and Tarski, where $G$ is the group of rotations of space.

#### Common errors

1. `MulAction.toPerm` needs a group. For a monoid, an element does not act by a bijection in general, and the right map is `MulAction.toEndHom`. For one unit of a monoid, use `IsUnit.smul_bijective`.
2. `MulAction.IsPretransitive` holds for an empty type. A statement that needs a point, for example that $\alpha$ is the orbit of one point, needs a Nonempty hypothesis or a given point in addition.
3. The structure `Equidecomp X G` records only that some finite witness exists. The function `Equidecomp.witness` chooses one, so a lemma cannot compute its value. Use `Equidecomp.isDecompOn` to get the property of the chosen set, and do not expect the witness of `Equidecomp.trans` to be a given product of two sets.

### Exercises

1. (A) Let $G$ act on $\alpha$. Show that the kernel of `MulAction.toPermHom G α` is the intersection of the stabilizers of all points. Deduce that the action is faithful if and only if this intersection is trivial.
2. (A) Let $f : N \to M$ be a homomorphism and let $M$ act on $\alpha$. Show that the orbits of $N$ under the action by `MulAction.compHom` are contained in the orbits of $M$, and that they are equal when $f$ is surjective.
3. (A) Let $M$ be a monoid. Show that the actions of $M$ on itself by left and by right multiplication are faithful. Let $S$ be a set with at least two elements and the product $x y = y$. Show that $S$ is a semigroup and that its action on itself by left multiplication is not faithful.
4. (B) Let $G$ be a group and $H$ a subgroup. Show that $G$ acts pretransitively on $G/H$, and that this action is faithful if and only if $H$ contains no nontrivial normal subgroup of $G$.
5. (B) Let $\mathbb{Z}$ act on itself by addition. Show that $\mathbb{N}$ and $\mathbb{N} \cup \{-1\}$ are equidecomposable. Show that the set of even integers and $\mathbb{Z}$ are not equidecomposable, by a count of the points in a long interval.
6. (C) Let $G$ act on $X$. Show that equidecomposability is reflexive, symmetric and transitive. Show that if $A$ is equidecomposable with $B$, $C$ is equidecomposable with $D$, $A \cap C = \emptyset$ and $B \cap D = \emptyset$, then $A \cup C$ is equidecomposable with $B \cup D$.

### Reference

<?reference?>
