---
title: Galois connections
kind: theory
modules:
  - Mathlib.Order.GaloisConnection.Defs
  - Mathlib.Order.GaloisConnection.Basic
explains:
  E3: [GaloisConnection]
  E2: [GaloisConnection.monotone_l, GaloisConnection.l_u_le, GaloisConnection.le_u_l, GaloisConnection.l_sup, GaloisInsertion]
  E1: [GaloisConnection.monotone_u, GaloisConnection.le_iff_le, GaloisConnection.u_l_u_eq_u, GaloisConnection.u_inf, GaloisConnection.compose, GaloisConnection.l_bot, GaloisConnection.u_top, Set.image_subset_iff, Int.le_floor, Int.gc_coe_floor]
families: []
requires: [V04.C02, V04.C03]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V04/C06/Examples.lean
  - MathlibHandbook/V04/C06/Exercises.lean
  - MathlibHandbook/V04/C06/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Galois connections

### Overview

Many pairs of maps in mathematics satisfy one condition: $l(a) \le b \iff a \le u(b)$. The image and the preimage of a function satisfy it. The cast from `ℤ` to `ℝ` and the floor function satisfy it. The map from a set to the subgroup that it generates and the map from a subgroup to its carrier set satisfy it. Mathlib calls such a pair a Galois connection, and it proves many lemmas once for all of them. The lower map $l$ keeps all suprema, and the upper map $u$ keeps all infima. This section shows the definition, the main examples, and the lemmas that follow from the condition.

### Definitions

**Definition (Galois connection).** Let $\alpha$ and $\beta$ be preorders. A pair of functions $l : \alpha \to \beta$ and $u : \beta \to \alpha$ is a Galois connection if $l(a) \le b \iff a \le u(b)$ for all $a \in \alpha$ and $b \in \beta$. The map $l$ is the lower adjoint, and $u$ is the upper adjoint.

**Definition (Galois insertion).** A Galois insertion is a Galois connection with $l(u(b)) = b$ for each $b$. In Mathlib, `GaloisInsertion l u` is a structure with a choice function, so that a proof can give a better definition of $l$ on the elements of the form $u(b)$.

### Theorems and proofs

**Theorem (Unit and counit).** For a Galois connection, $a \le u(l(a))$ and $l(u(b)) \le b$.

*Proof.* The condition with $b = l(a)$ gives $l(a) \le l(a) \iff a \le u(l(a))$, and the left side is true. The condition with $a = u(b)$ gives $l(u(b)) \le b \iff u(b) \le u(b)$, and the right side is true. $\square$

**Theorem (Monotonicity).** The maps $l$ and $u$ of a Galois connection are monotone.

*Proof.* Let $a_1 \le a_2$. By the unit, $a_2 \le u(l(a_2))$, so $a_1 \le u(l(a_2))$. The condition gives $l(a_1) \le l(a_2)$. The proof for $u$ is dual. $\square$

**Theorem (The lower adjoint keeps the supremum).** In lattices, $l(a_1 \sqcup a_2) = l(a_1) \sqcup l(a_2)$.

*Proof.* For each $b$, the condition and the universal property of the sup give $l(a_1 \sqcup a_2) \le b \iff a_1 \sqcup a_2 \le u(b) \iff a_1 \le u(b) \land a_2 \le u(b) \iff l(a_1) \le b \land l(a_2) \le b \iff l(a_1) \sqcup l(a_2) \le b$. Two elements with the same upper bounds are equal in a partial order. $\square$

::: mathlib
`GaloisConnection` · `Mathlib.Order.GaloisConnection.Defs`

The definition is the plain condition `∀ a b, l a ≤ b ↔ a ≤ u b`, so `Iff.rfl` unfolds it. A proof of `gc : GaloisConnection l u` applies as `(gc a b).mp`, and `gc.le_iff_le` is the same equivalence with implicit arguments.

<?decl GaloisConnection?>
:::

::: mathlib
`GaloisConnection.l_u_le` · `Mathlib.Order.GaloisConnection.Defs`

The lemma is the counit, and `GaloisConnection.le_u_l` is the unit. The lemma `GaloisConnection.u_l_u_eq_u` follows from the two.

<?decl GaloisConnection.l_u_le?>
:::

::: mathlib
`GaloisConnection.l_sup` · `Mathlib.Order.GaloisConnection.Basic`

The lemma needs lattices on the two sides. The dual lemma `GaloisConnection.u_inf` states that $u$ keeps the infimum, and the file has the versions for `sSup`, `iSup`, `sInf` and `iInf`.

<?decl GaloisConnection.l_sup?>
:::

### Examples

**Example (The definition).**

<?lean MathlibHandbook/V04/C06/Examples.lean#def?>

**Example (Image and preimage).** The condition is the lemma `Set.image_subset_iff`: $f(s) \subseteq t \iff s \subseteq f^{-1}(t)$.

<?lean MathlibHandbook/V04/C06/Examples.lean#image?>

**Example (The floor).** The cast from `ℤ` is the lower adjoint, and the floor is the upper adjoint. The connection is `Int.gc_coe_floor`.

<?lean MathlibHandbook/V04/C06/Examples.lean#floor?>

**Example (Monotonicity).**

<?lean MathlibHandbook/V04/C06/Examples.lean#monotone?>

**Example (Unit and counit).**

<?lean MathlibHandbook/V04/C06/Examples.lean#unit?>

**Example (The supremum).** For the image, this lemma gives $f(s \cup t) = f(s) \cup f(t)$ with no extra work.

<?lean MathlibHandbook/V04/C06/Examples.lean#sup?>

**Counterexample (The lower adjoint does not keep the infimum).** The image keeps the union, but it does not keep the intersection. For the constant map $f : \{0, 1\} \to \{0\}$, the sets $\{0\}$ and $\{1\}$ have an empty intersection, but their images are both $\{0\}$.

### The library around it

Mathlib uses Galois connections to define the closure in many structures. The span of a set in a module, the subgroup that a set generates, and the topology that a family of sets generates each come from a Galois insertion, for example `Subgroup.gi`. A Galois insertion then gives a complete lattice structure on the target from the structure on the source, with `GaloisInsertion.liftCompleteLattice`. The lemma `GaloisConnection.compose` composes two connections. The lemmas `GaloisConnection.l_bot` and `GaloisConnection.u_top` state that $l(\bot) = \bot$ and $u(\top) = \top$. For the floor and the ceiling on an ordered ring, see `Mathlib.Algebra.Order.Floor.Defs`.

### Exercises

1. (A) Give the lower and the upper adjoint for the floor function on `ℝ`.
2. (A) State the condition of a Galois connection for `Set.image f` and `Set.preimage f`.
3. (B) Show that $u \circ l \circ u = u$ for a Galois connection.
4. (B) Show that the ceiling $\lceil \cdot \rceil : \mathbb{R} \to \mathbb{Z}$ is the lower adjoint of the cast from `ℤ` to `ℝ`.
5. (B) Show that for each $n > 0$ in `ℕ`, the maps $a \mapsto a \cdot n$ and $b \mapsto b / n$ are a Galois connection.
6. (L) Prove the counit $l(u(b)) \le b$. The solution is `l_u_le_example`.
7. (L) Prove that the upper adjoint keeps the infimum. The solution is `u_inf_example`.
8. (L) Prove that the image of a union is the union of the images. The solution is `image_union_example`.

### Notes and history

Ore introduced Galois connections in 1944, and he named them after the correspondence of Galois between subgroups and intermediate fields. In category theory, a Galois connection is an adjunction between two preorders, and the lemmas of this section are special cases of the lemmas on adjunctions.

### Reference

<?reference?>
