---
title: The symmetric and the alternating groups
kind: theory
modules:
  - Mathlib.GroupTheory.Perm.Sign
  - Mathlib.GroupTheory.SpecificGroups.Alternating
explains:
  E3: [Equiv.Perm.sign]
  E2: [Equiv.Perm.sign_swap, Equiv.Perm.sign_mul, Equiv.Perm.cycleType, alternatingGroup]
  E1: auto
families: []
requires: [V05.C05]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V05/C07/Examples.lean
  - MathlibHandbook/V05/C07/Exercises.lean
  - MathlibHandbook/V05/C07/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The symmetric and the alternating groups

### Overview

A permutation of a set $\alpha$ is a bijection from $\alpha$ to itself. The permutations form a group under composition, the symmetric group. For a finite set, each permutation has a sign, $1$ or $-1$, and the sign is a homomorphism. Its kernel is the alternating group. In Mathlib a permutation is an equivalence `Equiv.Perm α`, so each lemma about equivalences from Volume 1 applies to it. This section shows the group of permutations, the transpositions, the sign and the alternating group.

### Definitions

**Definition (Permutation).** A permutation of $\alpha$ is a bijection $\sigma : \alpha \to \alpha$. In Mathlib it is `Equiv.Perm α`, which is `α ≃ α`. The product `σ * τ` is the composite that applies `τ` first, and `1` is the identity.

**Definition (Transposition).** For $a \neq b$, the transposition $(a\ b)$ exchanges $a$ and $b$ and fixes each other point. In Mathlib it is `Equiv.swap a b`. When $a = b$ the swap is the identity.

**Definition (Sign).** Each permutation of a finite set is a product of transpositions. The sign of $\sigma$ is $(-1)^k$, where $k$ is the number of transpositions in such a product. In Mathlib it is `Equiv.Perm.sign σ`, an element of the group of units `ℤˣ`.

**Definition (Alternating group).** The alternating group $A_n$ is the set of the permutations with sign $1$. In Mathlib it is `alternatingGroup α`, the kernel of the sign.

**Definition (Cycle type).** The cycle type of $\sigma$ is the multiset of the lengths of its cycles of length at least $2$. In Mathlib it is `σ.cycleType`.

### Theorems and proofs

**Theorem (Order of the symmetric group).** If $|\alpha| = n$, then there are $n!$ permutations of $\alpha$.

*Proof.* A permutation has $n$ choices for the image of the first point, $n - 1$ for the second, and so on. $\square$

**Theorem (The sign is well defined).** The parity of the number of transpositions in a product that gives $\sigma$ depends only on $\sigma$.

*Proof.* Order $\alpha$ and count the inversions, the pairs $i < j$ with $\sigma(i) > \sigma(j)$. A transposition changes the number of inversions by an odd number. So $(-1)^{\text{inversions}}$ is $(-1)^k$ for each product of $k$ transpositions. $\square$

**Theorem (The sign is a homomorphism).** $\operatorname{sign}(\sigma \tau) = \operatorname{sign}(\sigma) \operatorname{sign}(\tau)$.

*Proof.* Join a product of $k$ transpositions for $\sigma$ and a product of $l$ transpositions for $\tau$. This gives $k + l$ transpositions for $\sigma \tau$. $\square$

**Theorem (Index of the alternating group).** If $|\alpha| \ge 2$, then $A_\alpha$ has index $2$.

*Proof.* A transposition has sign $-1$, so the sign is onto $\{1, -1\}$. By the first isomorphism theorem of Chapter 5, the quotient by the kernel has $2$ elements. $\square$

::: mathlib
`Equiv.Perm.sign` · `Mathlib.GroupTheory.Perm.Sign`

The sign as a homomorphism `Perm α →* ℤˣ`. It needs `DecidableEq α` and `Fintype α`. The definition counts inversions on `Fin n` and moves the result along an equivalence. The proofs use the induction `Equiv.Perm.swap_induction_on` instead.

<?decl Equiv.Perm.sign?>
:::

::: mathlib
`Equiv.Perm.sign_swap` · `Mathlib.GroupTheory.Perm.Sign`

A transposition has the sign $-1$. The lemma needs the proof of $a \neq b$, and `decide` gives it for concrete elements of `Fin n`.

<?decl Equiv.Perm.sign_swap?>
:::

::: mathlib
`Equiv.Perm.sign_mul` · `Mathlib.GroupTheory.Perm.Sign`

The sign respects products. The sign is a bundled homomorphism, so `map_mul` gives the same fact.

<?decl Equiv.Perm.sign_mul?>
:::

::: mathlib
`Equiv.Perm.cycleType` · `Mathlib.GroupTheory.Perm.Cycle.Type`

The cycle type as a `Multiset ℕ`. Two permutations are conjugate if and only if they have the same cycle type, by `Equiv.Perm.isConj_iff_cycleType_eq`.

<?decl Equiv.Perm.cycleType?>
:::

::: mathlib
`alternatingGroup` · `Mathlib.GroupTheory.SpecificGroups.Alternating`

The alternating group as a `Subgroup (Perm α)`. The lemma `Equiv.Perm.mem_alternatingGroup` says that $\sigma$ is in it if and only if its sign is $1$.

<?decl alternatingGroup?>
:::

### Examples

**Example (The order of a symmetric group).** There are $3! = 6$ permutations of `Fin 3`.

<?lean MathlibHandbook/V05/C07/Examples.lean#perm?>

**Example (A transposition).**

<?lean MathlibHandbook/V05/C07/Examples.lean#swap?>

**Example (The sign of a transposition).**

<?lean MathlibHandbook/V05/C07/Examples.lean#sign_swap?>

**Example (The sign of a product).**

<?lean MathlibHandbook/V05/C07/Examples.lean#sign_mul?>

**Example (The alternating group).** The subgroup `alternatingGroup (Fin 3)` has index $2$.

<?lean MathlibHandbook/V05/C07/Examples.lean#alternating?>

### The library around it

The cycles of a permutation are in `Mathlib.GroupTheory.Perm.Cycle.Basic`, with the predicate `Equiv.Perm.IsCycle`. The support of $\sigma$, the set of the points that it moves, is `Equiv.Perm.support`. The file `Mathlib.GroupTheory.Perm.Fin` has the cycles of `Fin n`, and `isCycle_finRotate` says that the rotation `finRotate` is a cycle. The concrete groups, such as the dihedral group `DihedralGroup n`, are in `Mathlib.GroupTheory.SpecificGroups`. To compute with a concrete permutation of `Fin n`, `decide` often works, because the type is finite and the equality is decidable.

### Exercises

1. (A) Give the sign of a cycle of length $3$.
2. (A) Explain why `σ * τ` applies `τ` first.
3. (B) Show that $A_n$ is the subgroup that the cycles of length $3$ generate, for $n \ge 3$.
4. (B) Show that the sign of a cycle of length $k$ is $(-1)^{k-1}$.
5. (L) Prove that a transposition of `Fin 4` is its own inverse. The solution is `swap_mul_self_example`.
6. (L) Prove that $\sigma$ and $\sigma^{-1}$ have the same sign. The solution is `sign_inv_example`.
7. (L) Prove that a product of two transpositions of `Fin 4` is in $A_4$. The solution is `mem_alternating_example`.
8. (L) Prove that $A_4$ has $12$ elements. The solution is `card_alternating_example`.

### Notes and history

Lagrange, Ruffini and Cauchy studied permutations of the roots of a polynomial near 1800. Cauchy proved that the sign is well defined in 1815. Galois theory shows that the general quintic has no solution by radicals, and the reason is that $A_5$ is simple. Mathlib proves that $A_n$ is simple for $n \ge 5$, in the theorem `alternatingGroup.isSimpleGroup`.

### Reference

<?reference?>
