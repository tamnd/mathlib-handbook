---
title: Subgroups, kernels and ranges
kind: theory
modules:
  - Mathlib.Algebra.Group.Subgroup.Defs
  - Mathlib.Algebra.Group.Subgroup.Lattice
  - Mathlib.Algebra.Group.Subgroup.Ker
explains:
  E3: [Subgroup, MonoidHom.ker_eq_bot_iff]
  E2: [Subgroup.closure, Subgroup.mem_closure, MonoidHom.ker, MonoidHom.range, Subgroup.mul_mem, Subgroup.inv_mem, Subgroup.one_mem]
  E1: auto
families: []
requires: [V05.C02]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V05/C03/Examples.lean
  - MathlibHandbook/V05/C03/Exercises.lean
  - MathlibHandbook/V05/C03/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Subgroups, kernels and ranges

### Overview

A subgroup is a subset of a group that is a group under the same product. In Mathlib, `Subgroup G` is a structure: a set with three proofs of closure. The subgroups of $G$ are ordered by inclusion, and they form a complete lattice. Two subgroups come with each homomorphism $f$: the kernel and the range. This section shows the structure, the lattice, the subgroup that a set generates, and the test for an injective homomorphism.

### Definitions

**Definition (Subgroup).** A subgroup of $G$ is a set $H \subseteq G$ with $1 \in H$, with $a \cdot b \in H$ for $a, b \in H$, and with $a^{-1} \in H$ for $a \in H$. In Mathlib, `H : Subgroup G` coerces to a set, and `x ∈ H` is the membership.

**Definition (Lattice of subgroups).** The order $H \le K$ is inclusion. The bottom subgroup $\bot$ is $\{1\}$, the top subgroup $\top$ is $G$, and the meet $H \sqcap K$ is the intersection. The join $H \sqcup K$ is the subgroup that $H \cup K$ generates.

**Definition (Closure).** The closure of a set $s \subseteq G$ is the smallest subgroup that contains $s$. It is `Subgroup.closure s`.

**Definition (Kernel and range).** For a homomorphism $f : G \to H$, the kernel is $\{x \in G : f(x) = 1\}$ and the range is $\{f(x) : x \in G\}$. They are `f.ker : Subgroup G` and `f.range : Subgroup H`.

### Theorems and proofs

**Theorem (Closure is the smallest).** If $s \subseteq K$ for a subgroup $K$, then the closure of $s$ is in $K$.

*Proof.* The closure is the intersection of all subgroups that contain $s$. The subgroup $K$ is one of them. $\square$

**Theorem (Kernel test).** A homomorphism $f$ is injective if and only if its kernel is $\{1\}$.

*Proof.* If $f$ is injective and $f(x) = 1 = f(1)$, then $x = 1$. For the converse, let $f(a) = f(b)$. Then $f(a^{-1} \cdot b) = f(a)^{-1} \cdot f(b) = 1$, so $a^{-1} \cdot b = 1$ and $a = b$. $\square$

**Theorem (Kernel and range are subgroups).** The kernel and the range of a homomorphism are subgroups.

*Proof.* Each closure axiom follows from `map_one`, `map_mul` and `map_inv`. For example, $f(a) = 1$ and $f(b) = 1$ give $f(a \cdot b) = 1$. $\square$

::: mathlib
`Subgroup` · `Mathlib.Algebra.Group.Subgroup.Defs`

The structure extends `Submonoid G` with the field `inv_mem'`. Use the lemmas `Subgroup.one_mem`, `Subgroup.mul_mem` and `Subgroup.inv_mem` in a proof. Two subgroups with the same elements are equal by `Subgroup.ext`.

<?decl Subgroup?>
:::

::: mathlib
`Subgroup.mul_mem` · `Mathlib.Algebra.Group.Subgroup.Defs`

The lemma is the closure under products. Its general form `MulMemClass.mul_mem` holds for each class of subobjects with `MulMemClass`.

<?decl Subgroup.mul_mem?>
:::

::: mathlib
`Subgroup.inv_mem` · `Mathlib.Algebra.Group.Subgroup.Defs`

The closure under inverses. With `Subgroup.mul_mem` it gives `Subgroup.div_mem`.

<?decl Subgroup.inv_mem?>
:::

::: mathlib
`Subgroup.one_mem` · `Mathlib.Algebra.Group.Subgroup.Defs`

The unit is in each subgroup. A `simp` call proves it with no argument.

<?decl Subgroup.one_mem?>
:::

::: mathlib
`Subgroup.closure` · `Mathlib.Algebra.Group.Subgroup.Lattice`

The closure is defined as the infimum of the subgroups that contain the set. The lemma `Subgroup.closure_le` is its universal property.

<?decl Subgroup.closure?>
:::

::: mathlib
`Subgroup.mem_closure` · `Mathlib.Algebra.Group.Subgroup.Lattice`

The lemma says that $x$ is in the closure of $s$ if and only if $x$ is in each subgroup that contains $s$. For a proof by induction on the words, use `Subgroup.closure_induction`.

<?decl Subgroup.mem_closure?>
:::

::: mathlib
`MonoidHom.ker` · `Mathlib.Algebra.Group.Subgroup.Ker`

The kernel of a homomorphism of groups. The lemma `MonoidHom.mem_ker` unfolds the membership.

<?decl MonoidHom.ker?>
:::

::: mathlib
`MonoidHom.range` · `Mathlib.Algebra.Group.Subgroup.Ker`

The range as a subgroup of the target. The lemma `MonoidHom.mem_range` says that $y$ is in it if and only if $y = f(x)$ for some $x$.

<?decl MonoidHom.range?>
:::

::: mathlib
`MonoidHom.ker_eq_bot_iff` · `Mathlib.Algebra.Group.Subgroup.Ker`

The kernel test for injective maps. It is the usual way to prove that a homomorphism is injective.

<?decl MonoidHom.ker_eq_bot_iff?>
:::

### Examples

**Example (The closure axioms).**

<?lean MathlibHandbook/V05/C03/Examples.lean#mem?>

**Example (The lattice).** The bottom subgroup and the meet unfold with `Subgroup.mem_bot` and `Subgroup.mem_inf`.

<?lean MathlibHandbook/V05/C03/Examples.lean#lattice?>

**Example (The closure).**

<?lean MathlibHandbook/V05/C03/Examples.lean#closure?>

**Example (The kernel).**

<?lean MathlibHandbook/V05/C03/Examples.lean#ker?>

**Example (Injective homomorphisms).**

<?lean MathlibHandbook/V05/C03/Examples.lean#injective?>

### The library around it

The subgroups of $G$ are a `CompleteLattice`, so each lemma of Volume 1 about lattices applies to them. A subgroup `H` is also a group: the coercion `↥H` is the subtype of its elements, and it has an instance of `Group`. The map and the comap of a subgroup along a homomorphism are `Subgroup.map` and `Subgroup.comap`. The additive copy is `AddSubgroup`. To prove that $x$ is in a subgroup, `simp` with the membership lemmas often works.

### Exercises

1. (A) Give the elements of the bottom subgroup of a group.
2. (A) Explain why `↥H` is a group for `H : Subgroup G`.
3. (B) Show that the union of two subgroups is a subgroup only if one of them contains the other.
4. (B) Show that the closure of $\{a\}$ is the set of the powers $a^n$ with $n \in \mathbb{Z}$.
5. (L) Prove that each element is in the top subgroup. The solution is `mem_top_example`.
6. (L) Prove that $a, b \in H$ gives $a \cdot b^{-1} \in H$. The solution is `div_mem_example`.
7. (L) Prove that $f(x)$ is in the range of $f$. The solution is `mem_range_example`.

### Notes and history

The lattice of subgroups was a theme of the work of Dedekind and of Ore in the 1930s. In Mathlib the lattice is a complete lattice by a general construction: each family of subgroups has an intersection, and that fact gives the join. The bundled `Subgroup` replaced the Lean 3 predicate `is_subgroup`.

### Reference

<?reference?>
