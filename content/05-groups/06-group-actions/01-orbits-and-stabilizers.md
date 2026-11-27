---
title: Orbits and stabilizers
kind: theory
modules:
  - Mathlib.Algebra.Group.Action.Defs
  - Mathlib.GroupTheory.GroupAction.Defs
  - Mathlib.GroupTheory.GroupAction.Quotient
explains:
  E3: [MulAction.card_orbit_mul_card_stabilizer_eq_card_group]
  E2: [MulAction, MulAction.orbit, MulAction.stabilizer, MulAction.mem_orbit_iff, MulAction.mem_stabilizer_iff, MulAction.orbitEquivQuotientStabilizer]
  E1: auto
families: []
requires: [V05.C04]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V05/C06/Examples.lean
  - MathlibHandbook/V05/C06/Exercises.lean
  - MathlibHandbook/V05/C06/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Orbits and stabilizers

### Overview

A group action is a way for a group to move the points of a set. Each $g \in G$ gives a map $x \mapsto g \cdot x$, the unit gives the identity, and a product gives a composite. In Mathlib the action is the class `MulAction G X`, with the notation `g • x`. Each point has an orbit, the points that it can move to, and a stabilizer, the elements that fix it. The orbit stabilizer theorem connects the two sizes. This section shows the class, the two sets, and the theorem.

### Definitions

**Definition (Action).** An action of a group $G$ on a set $X$ is a map $G \times X \to X$, written $g \cdot x$, with $1 \cdot x = x$ and $g \cdot (h \cdot x) = (g h) \cdot x$. In Mathlib it is `MulAction G X`, and the map has the notation `•`.

**Definition (Orbit).** The orbit of $x$ is $G \cdot x = \{g \cdot x : g \in G\}$. In Mathlib it is `MulAction.orbit G x : Set X`.

**Definition (Stabilizer).** The stabilizer of $x$ is $G_x = \{g \in G : g \cdot x = x\}$. It is a subgroup, `MulAction.stabilizer G x : Subgroup G`.

**Definition (Transitive action).** An action is transitive if it has only one orbit. In Mathlib the class is `MulAction.IsPretransitive G X`. It does not ask that $X$ has an element.

### Theorems and proofs

**Theorem (Orbits are a partition).** Two orbits are equal or disjoint.

*Proof.* If $z \in G \cdot x$ and $z \in G \cdot y$, then $g \cdot x = h \cdot y$ for some $g$ and $h$. So $x = g^{-1} h \cdot y$ is in $G \cdot y$, and $G \cdot x \subseteq G \cdot y$. The other inclusion is the same. $\square$

**Theorem (Orbit and cosets).** The map $g G_x \mapsto g \cdot x$ is a bijection from $G / G_x$ to the orbit of $x$.

*Proof.* $g \cdot x = h \cdot x$ if and only if $g^{-1} h \cdot x = x$, that is $g^{-1} h \in G_x$. That is the condition for $g G_x = h G_x$. So the map is well defined and injective. It is onto the orbit by the definition of the orbit. $\square$

**Theorem (Orbit stabilizer).** If $G$ is finite, then $|G \cdot x| \cdot |G_x| = |G|$.

*Proof.* By the bijection, $|G \cdot x| = [G : G_x]$. Apply the theorem of Lagrange to $G_x$. $\square$

::: mathlib
`MulAction` · `Mathlib.Algebra.Group.Action.Defs`

The class adds two axioms to the notation `•`: the unit acts as the identity, and a product acts as a composite. The lemmas are `one_smul` and `smul_smul`. The class needs only a monoid. The additive copy is `AddAction`, with the notation `+ᵥ`.

<?decl MulAction?>
:::

::: mathlib
`MulAction.orbit` · `Mathlib.GroupTheory.GroupAction.Defs`

The orbit is the range of the map $g \mapsto g \cdot x$. The lemma `MulAction.mem_orbit_self` says that $x$ is in its orbit.

<?decl MulAction.orbit?>
:::

::: mathlib
`MulAction.stabilizer` · `Mathlib.GroupTheory.GroupAction.Defs`

The stabilizer as a `Subgroup G`. For a monoid, `MulAction.stabilizerSubmonoid` gives the submonoid.

<?decl MulAction.stabilizer?>
:::

::: mathlib
`MulAction.mem_orbit_iff` · `Mathlib.GroupTheory.GroupAction.Defs`

The membership in an orbit: $y \in G \cdot x$ if and only if $g \cdot x = y$ for some $g$.

<?decl MulAction.mem_orbit_iff?>
:::

::: mathlib
`MulAction.mem_stabilizer_iff` · `Mathlib.GroupTheory.GroupAction.Defs`

The membership in a stabilizer. A `simp` call uses it to unfold the goal.

<?decl MulAction.mem_stabilizer_iff?>
:::

::: mathlib
`MulAction.orbitEquivQuotientStabilizer` · `Mathlib.GroupTheory.GroupAction.Quotient`

The bijection between the orbit and the cosets of the stabilizer, as an equivalence. It is the core of the theorem below.

<?decl MulAction.orbitEquivQuotientStabilizer?>
:::

::: mathlib
`MulAction.card_orbit_mul_card_stabilizer_eq_card_group` · `Mathlib.GroupTheory.GroupAction.Quotient`

The orbit stabilizer theorem with `Fintype.card`. It needs instances `Fintype` for the orbit and the stabilizer.

<?decl MulAction.card_orbit_mul_card_stabilizer_eq_card_group?>
:::

### Examples

**Example (The axioms).** The lemmas `one_smul` and `smul_smul` are the two axioms.

<?lean MathlibHandbook/V05/C06/Examples.lean#action?>

**Example (The orbit).**

<?lean MathlibHandbook/V05/C06/Examples.lean#orbit?>

**Example (The stabilizer).**

<?lean MathlibHandbook/V05/C06/Examples.lean#stabilizer?>

**Example (The orbit stabilizer theorem).**

<?lean MathlibHandbook/V05/C06/Examples.lean#orbit_stabilizer?>

**Example (The regular action).** Mathlib has an instance for the action of $G$ on itself by left multiplication.

<?lean MathlibHandbook/V05/C06/Examples.lean#regular?>

### The library around it

The relation "same orbit" is `MulAction.orbitRel`, and its quotient is the set of the orbits. The class equation and the Burnside lemma use it. The fixed points of the action are `MulAction.fixedPoints`. The action of a group on itself by conjugation is `ConjAct G`, and Chapter 8 uses it for the Sylow theorems. The classes `DistribMulAction` and `Module` extend `MulAction`, for an action that respects addition. A lemma that needs an action of a group, not of a monoid, often has the prefix `smul_` and a name like `smul_left_cancel`.

### Exercises

1. (A) Give the orbit of $1$ in the action of $G$ on itself by left multiplication.
2. (A) Explain why the stabilizer is a subgroup.
3. (B) Show that a group of order $p^k$ with $p$ prime that acts on a finite set $X$ has $|X| \equiv |X^G| \pmod p$, where $X^G$ is the set of the fixed points.
4. (B) Show that the stabilizers of two points in the same orbit are conjugate.
5. (L) Prove that $x$ is in its orbit. The solution is `mem_orbit_self_example`.
6. (L) Prove that $g \cdot x$ is in the orbit of $x$. The solution is `smul_mem_orbit_example`.
7. (L) Prove that $1$ is in the stabilizer of $x$. The solution is `one_mem_stabilizer_example`.

### Notes and history

Groups started as groups of permutations and of symmetries, that is, as actions. The abstract group came later, with Cayley in 1854. Cayley also showed that each group acts faithfully on itself, so each group is a group of permutations. The orbit stabilizer theorem has no single author. It was known to Frobenius and to Burnside near 1900.

### Reference

<?reference?>
