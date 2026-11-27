---
title: Quotient groups and the first isomorphism theorem
kind: theory
modules:
  - Mathlib.GroupTheory.QuotientGroup.Defs
  - Mathlib.GroupTheory.QuotientGroup.Basic
explains:
  E3: [QuotientGroup.quotientKerEquivRange]
  E2: [Subgroup.Normal, Subgroup.Normal.conj_mem, QuotientGroup.mk, QuotientGroup.eq, QuotientGroup.lift]
  E1: auto
families: []
requires: [V05.C04]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V05/C05/Examples.lean
  - MathlibHandbook/V05/C05/Exercises.lean
  - MathlibHandbook/V05/C05/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Quotient groups and the first isomorphism theorem

### Overview

A normal subgroup is a subgroup that is closed under conjugation. For a normal subgroup $N$, the cosets of $N$ form a group, the quotient $G / N$. The kernel of each homomorphism is normal, and the first isomorphism theorem says that $G / \ker f$ is isomorphic to the range of $f$. In Mathlib, `Subgroup.Normal` is a class, and the quotient `G ⧸ N` has a group instance when it can find `N.Normal`. This section shows the class, the quotient map, its universal property and the isomorphism theorem.

### Definitions

**Definition (Normal subgroup).** A subgroup $N$ of $G$ is normal if $g \cdot n \cdot g^{-1} \in N$ for each $n \in N$ and $g \in G$. In Mathlib it is the class `N.Normal`.

**Definition (Quotient group).** For a normal subgroup $N$, the quotient $G / N$ is the set of the left cosets $aN$ with the product $aN \cdot bN = (a \cdot b) N$. In Mathlib it is `G ⧸ N`. The class of $a$ is `(a : G ⧸ N)`, a coercion, or `QuotientGroup.mk a`.

**Definition (Quotient map).** The map $a \mapsto aN$ is a homomorphism $G \to G / N$. As a bundled homomorphism it is `QuotientGroup.mk' N`.

### Theorems and proofs

**Theorem (Kernels are normal).** The kernel of a homomorphism $f$ is a normal subgroup.

*Proof.* If $f(n) = 1$, then $f(g \cdot n \cdot g^{-1}) = f(g) \cdot 1 \cdot f(g)^{-1} = 1$. $\square$

**Theorem (The product is well defined).** If $N$ is normal, $aN = a'N$ and $bN = b'N$, then $(a \cdot b) N = (a' \cdot b') N$.

*Proof.* Put $n = a^{-1} a'$ and $m = b^{-1} b'$, both in $N$. Then $(a b)^{-1} (a' b') = b^{-1} n b' = (b^{-1} n b) \cdot m$. The first factor is in $N$ because $N$ is normal. $\square$

**Theorem (Universal property).** If $f : G \to H$ is a homomorphism and $N \le \ker f$, then there is one homomorphism $\bar f : G / N \to H$ with $\bar f(aN) = f(a)$.

*Proof.* If $aN = bN$, then $a^{-1} b \in N$, so $f(a)^{-1} f(b) = 1$ and $f(a) = f(b)$. So $\bar f$ is well defined. It is a homomorphism because $f$ is one. $\square$

**Theorem (First isomorphism theorem).** For a homomorphism $f : G \to H$, the group $G / \ker f$ is isomorphic to the range of $f$.

*Proof.* Apply the universal property with $N = \ker f$. The map $\bar f$ is onto the range. If $\bar f(aN) = 1$, then $a \in \ker f$, so $aN$ is the unit. By the kernel test, $\bar f$ is injective. $\square$

::: mathlib
`Subgroup.Normal` · `Mathlib.Algebra.Group.Subgroup.Defs`

The class has the one field `conj_mem`. It is a class so that the instance search can find it for `G ⧸ N`.

<?decl Subgroup.Normal?>
:::

::: mathlib
`Subgroup.Normal.conj_mem` · `Mathlib.Algebra.Group.Subgroup.Defs`

The conjugate $g \cdot n \cdot g^{{-1}}$ is in $N$. The form `Subgroup.Normal.conj_mem'` gives $g^{{-1}} \cdot n \cdot g$.

<?decl Subgroup.Normal.conj_mem?>
:::

::: mathlib
`QuotientGroup.mk` · `Mathlib.GroupTheory.Coset.Defs`

The class of an element in `G ⧸ N`. It is an abbreviation, and the coercion `↑a` unfolds to it. The lemma `QuotientGroup.mk_mul` says that it respects products.

<?decl QuotientGroup.mk?>
:::

::: mathlib
`QuotientGroup.eq` · `Mathlib.GroupTheory.Coset.Defs`

Two classes are equal if and only if $a^{{-1}} \cdot b \in N$. The lemma needs no normality, because it is about left cosets.

<?decl QuotientGroup.eq?>
:::

::: mathlib
`QuotientGroup.lift` · `Mathlib.GroupTheory.QuotientGroup.Defs`

The universal property. It takes `N`, the homomorphism and the proof of `N ≤ f.ker`. The lemma `QuotientGroup.lift_mk` computes it on a class.

<?decl QuotientGroup.lift?>
:::

::: mathlib
`QuotientGroup.quotientKerEquivRange` · `Mathlib.GroupTheory.QuotientGroup.Basic`

The first isomorphism theorem as a term `G ⧸ f.ker ≃* f.range`. For a surjective $f$, `QuotientGroup.quotientKerEquivOfSurjective` gives $G / \ker f \cong H$.

<?decl QuotientGroup.quotientKerEquivRange?>
:::

### Examples

**Example (Conjugation).**

<?lean MathlibHandbook/V05/C05/Examples.lean#normal?>

**Example (The kernel is normal).** The instance `MonoidHom.normal_ker` gives the proof.

<?lean MathlibHandbook/V05/C05/Examples.lean#ker_normal?>

**Example (The quotient map respects products).**

<?lean MathlibHandbook/V05/C05/Examples.lean#mk_mul?>

**Example (Equal classes).**

<?lean MathlibHandbook/V05/C05/Examples.lean#eq?>

**Example (The universal property).**

<?lean MathlibHandbook/V05/C05/Examples.lean#lift?>

**Example (The first isomorphism theorem).** The term is `noncomputable`, because the inverse map chooses a preimage.

<?lean MathlibHandbook/V05/C05/Examples.lean#first_iso?>

### The library around it

The second and the third isomorphism theorems are `QuotientGroup.quotientInfEquivProdNormalQuotient` and `QuotientGroup.quotientQuotientEquivQuotient`. A map from one quotient to another is `QuotientGroup.map`. The quotient by the top subgroup is trivial, and the quotient by the bottom subgroup is isomorphic to $G$. The additive copy of `G ⧸ N` uses the same notation, and so does the quotient of a ring by an ideal. For a proof about all elements of `G ⧸ N`, start with `QuotientGroup.induction_on`, which reduces the goal to a class `↑a`.

### Exercises

1. (A) Explain why `G ⧸ N` needs the instance `N.Normal` to be a group.
2. (A) Give the kernel of the quotient map $G \to G / N$.
3. (B) Show that a subgroup of index $2$ is normal.
4. (B) Show that $G / N$ is commutative if and only if $a b a^{-1} b^{-1} \in N$ for all $a$ and $b$.
5. (L) Prove that the class of $1$ is the unit of `G ⧸ N`. The solution is `mk_one_example`.
6. (L) Prove that the kernel of `QuotientGroup.mk' N` is $N$. The solution is `ker_mk_example`.
7. (L) Prove that $g^{-1} \cdot n \cdot g \in N$ for $n \in N$. The solution is `conj_mem_example`.

### Notes and history

Galois found normal subgroups in 1830, as the subgroups that give a proper decomposition of a group. The quotient group and the isomorphism theorems came with Jordan and Hölder, and Emmy Noether gave them their modern form for modules and rings in the 1920s. In Mathlib the quotient is the quotient of a setoid, so each lemma about quotients from Volume 1 applies.

### Reference

<?reference?>
