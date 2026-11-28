---
title: Normal subgroups, quotient groups and the first isomorphism theorem
kind: theory
modules:
  - Mathlib.GroupTheory.QuotientGroup.Defs
  - Mathlib.GroupTheory.IndexNormal
  - Mathlib.Algebra.Quotient
  - Mathlib.GroupTheory.Subgroup.Simple
  - Mathlib.GroupTheory.QuotientGroup.Simple
  - Mathlib.GroupTheory.QuotientGroup.Finite
  - Mathlib.GroupTheory.QuotientGroup.ModEq
  - Mathlib.GroupTheory.Subgroup.Saturated
explains:
  E3: [QuotientGroup.quotientKerEquivRange]
  E2: [Subgroup.Normal, Subgroup.Normal.conj_mem, MonoidHom.normal_ker, Subgroup.normal_of_index_eq_two, Subgroup.center, QuotientGroup.Quotient.group, QuotientGroup.mk, QuotientGroup.eq, QuotientGroup.lift, QuotientGroup.quotientKerEquivOfSurjective]
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

## Normal subgroups, quotient groups and the first isomorphism theorem

### Overview

The cosets of a subgroup $N$ form a set $G/N$. When $N$ is normal, the product of representatives gives a group structure on $G/N$, the quotient group. The map $G \to G/N$ is then a surjective homomorphism with kernel $N$. Conversely, each kernel is normal. So the normal subgroups are exactly the kernels of homomorphisms.

The first isomorphism theorem says that each homomorphism $f$ factors as a quotient map, an isomorphism $G/\ker f \cong f(G)$, and an inclusion. It is the main tool to identify a quotient: to show $G/N \cong Q$, give a surjective homomorphism $G \to Q$ with kernel $N$. The next section proves the second and the third isomorphism theorems.

### Definitions

**Definition (Normal subgroup).** A subgroup $N \le G$ is normal if $g n g^{-1} \in N$ for each $g \in G$ and $n \in N$. One writes $N \trianglelefteq G$.

::: mathlib
`Subgroup.Normal` · `Mathlib.Algebra.Group.Subgroup.Defs`

A class with one field, `conj_mem`. Since it is a class, a normal subgroup is a subgroup `N` with an instance `[N.Normal]`, and the quotient group finds the instance by search. A proof of normality is written `⟨fun n hn g => ...⟩`.

<?decl Subgroup.Normal?>
:::

::: mathlib
`Subgroup.Normal.conj_mem` · `Mathlib.Algebra.Group.Subgroup.Defs`

The field: `n ∈ N → g * n * g⁻¹ ∈ N`. The form with $g^{-1} n g$ is `Subgroup.Normal.conj_mem'`.

<?decl Subgroup.Normal.conj_mem?>
:::

**Definition (Center).** The center $Z(G)$ is the set of the $z \in G$ with $z g = g z$ for each $g$. It is a subgroup by an exercise of Chapter 3.

::: mathlib
`Subgroup.center` · `Mathlib.GroupTheory.Subgroup.Center`

The center as a subgroup, with `Subgroup.mem_center_iff : z ∈ center G ↔ ∀ g, g * z = z * g`. The instance `Subgroup.instNormalCenter` makes it normal.

<?decl Subgroup.center?>
:::

**Definition (Quotient group).** Let $N \trianglelefteq G$. The quotient $G/N$ is the set of the left cosets $a N$ with the product $(a N)(b N) = (a b) N$. The quotient map is $\pi : G \to G/N$, $\pi(a) = a N$.

::: mathlib
`QuotientGroup.Quotient.group` · `Mathlib.GroupTheory.QuotientGroup.Defs`

The instance of `Group (G ⧸ N)` when `N.Normal`. Without the instance, `G ⧸ N` is only the type of the left cosets of Chapter 4.

<?decl QuotientGroup.Quotient.group?>
:::

::: mathlib
`QuotientGroup.mk` · `Mathlib.GroupTheory.Coset.Defs`

The quotient map as a function, written as the coercion `(a : G ⧸ N)`. The bundled homomorphism is `QuotientGroup.mk' N : G →* G ⧸ N`. The map is onto, by `QuotientGroup.mk_surjective`.

<?decl QuotientGroup.mk?>
:::

::: mathlib
`QuotientGroup.eq` · `Mathlib.GroupTheory.Coset.Defs`

The equality of classes: `(a : G ⧸ N) = b ↔ a⁻¹ * b ∈ N`. It is the theorem on cosets of Chapter 4 for the quotient type.

<?decl QuotientGroup.eq?>
:::

### Theorems and proofs

**Theorem (Forms of normality).** For a subgroup $N \le G$ the following are equivalent: (1) $N$ is normal; (2) $g N g^{-1} = N$ for each $g$; (3) $g N = N g$ for each $g$.

*Proof.* (1) gives (2): normality gives $g N g^{-1} \subseteq N$ for each $g$. Apply it to $g^{-1}$: $g^{-1} N g \subseteq N$, so $N \subseteq g N g^{-1}$. (2) gives (3): multiply $g N g^{-1} = N$ on the right by $g$. (3) gives (1): if $n \in N$, then $g n \in g N = N g$, so $g n = n' g$ for some $n' \in N$, and $g n g^{-1} = n' \in N$. $\square$

**Theorem (Kernels are normal).** Let $f : G \to H$ be a homomorphism. Then $\ker f \trianglelefteq G$.

*Proof.* If $f(n) = 1$, then $f(g n g^{-1}) = f(g) \cdot 1 \cdot f(g)^{-1} = 1$. $\square$

::: mathlib
`MonoidHom.normal_ker` · `Mathlib.Algebra.Group.Subgroup.Ker`

The theorem as an instance, so that `G ⧸ f.ker` is a group with no extra argument.

<?decl MonoidHom.normal_ker?>
:::

**Theorem (Index two).** A subgroup $N$ of index $2$ is normal.

*Proof.* The left cosets are $N$ and $G \setminus N$. The right cosets are $N$ and $G \setminus N$ too, because there are two of them by Chapter 4 and they partition $G$. Let $g \in G$. If $g \in N$, then $g N = N = N g$. If $g \notin N$, then $g N$ and $N g$ both contain $g$, so neither is $N$, and $g N = G \setminus N = N g$. So (3) holds. $\square$

::: mathlib
`Subgroup.normal_of_index_eq_two` · `Mathlib.GroupTheory.IndexNormal`

The theorem: `H.index = 2 → H.Normal`. It is often used for `alternatingGroup` in Chapter 7.

<?decl Subgroup.normal_of_index_eq_two?>
:::

**Theorem (The center is normal).** Each subgroup $N \le Z(G)$ is normal. In particular $Z(G) \trianglelefteq G$.

*Proof.* If $n \in Z(G)$, then $g n g^{-1} = n g g^{-1} = n \in N$. $\square$

**Theorem (The quotient group).** Let $N \trianglelefteq G$. The product $(a N)(b N) = (a b) N$ is well defined, $G/N$ is a group with unit $N$ and inverse $(a N)^{-1} = a^{-1} N$, and $\pi$ is a surjective homomorphism with kernel $N$. If $G$ is finite, then $|G/N| = |G|/|N|$.

*Proof.* Well defined: let $a' N = a N$ and $b' N = b N$. Then $a' = a n$ and $b' = b m$ with $n, m \in N$. So
$$a' b' = a n b m = a b (b^{-1} n b) m.$$
The element $b^{-1} n b$ is in $N$ by normality, applied to $g = b^{-1}$. So $a' b' \in a b N$, and $(a' b') N = (a b) N$. The axioms: $(a N \cdot b N) \cdot c N = ((a b) c) N = (a (b c)) N = a N \cdot (b N \cdot c N)$, and $N \cdot a N = a N = a N \cdot N$, and $a N \cdot a^{-1} N = N = a^{-1} N \cdot a N$. Each one follows from the same axiom in $G$. The map $\pi$ is a homomorphism by the definition of the product, and it is onto. Its kernel is the set of $a$ with $a N = N$, that is, $a \in N$. The last claim is Lagrange's theorem. $\square$

The converse holds too: if the rule $(a N)(b N) = (a b) N$ is well defined, then $N$ is normal. Indeed, for $n \in N$ the classes of $g n$ and $g$ are equal, so the classes of $g n g^{-1}$ and $g g^{-1} = 1$ are equal, and $g n g^{-1} \in N$.

**Theorem (Universal property of the quotient).** Let $N \trianglelefteq G$ and let $f : G \to H$ be a homomorphism with $N \le \ker f$. There is exactly one homomorphism $\bar f : G/N \to H$ with $\bar f(a N) = f(a)$.

*Proof.* Well defined: if $a N = b N$, then $a^{-1} b \in N \le \ker f$, so $f(a)^{-1} f(b) = 1$ and $f(a) = f(b)$. Homomorphism: $\bar f(a N \cdot b N) = f(a b) = f(a) f(b)$. Unique: each element of $G/N$ is some $a N$, and the value there is forced. $\square$

::: mathlib
`QuotientGroup.lift` · `Mathlib.GroupTheory.QuotientGroup.Defs`

The map $\bar f$ as `QuotientGroup.lift N f h : G ⧸ N →* H`, where `h` proves `N ≤ f.ker`. The computation rule `QuotientGroup.lift_mk` is a `simp` lemma.

<?decl QuotientGroup.lift?>
:::

**Theorem (First isomorphism theorem).** Let $f : G \to H$ be a homomorphism. Then $\bar f : G/\ker f \to f(G)$, $a \ker f \mapsto f(a)$, is an isomorphism.

*Proof.* Let $K = \ker f$. By the universal property, $\bar f$ is a well defined homomorphism to $H$, and its values are in $f(G)$. It is onto $f(G)$, since $f(a) = \bar f(a K)$. It is injective by the kernel test: if $\bar f(a K) = 1$, then $f(a) = 1$, so $a \in K$ and $a K = K$ is the unit. $\square$

::: mathlib
`QuotientGroup.quotientKerEquivRange` · `Mathlib.GroupTheory.QuotientGroup.Basic`

The isomorphism `G ⧸ f.ker ≃* f.range`. It is `noncomputable`, because the inverse map chooses a preimage. The injective map to `H` is `QuotientGroup.kerLift`, with `QuotientGroup.kerLift_injective`.

<?decl QuotientGroup.quotientKerEquivRange?>
:::

::: mathlib
`QuotientGroup.quotientKerEquivOfSurjective` · `Mathlib.GroupTheory.QuotientGroup.Basic`

The form for a surjective `f`: `G ⧸ f.ker ≃* H`. This is the form that identifies a quotient in practice.

<?decl QuotientGroup.quotientKerEquivOfSurjective?>
:::

### Examples

**Example (Integers modulo $n$).** The reduction $\mathbb{Z} \to \mathbb{Z}/n$ is a surjective homomorphism with kernel $n\mathbb{Z}$. So $\mathbb{Z}/n\mathbb{Z} \cong \mathbb{Z}/n$, and the quotient construction gives the integers modulo $n$ again. Every subgroup of $\mathbb{Z}$ is normal, because $\mathbb{Z}$ is commutative.

**Example (Matrices and the circle).** The determinant $\mathrm{GL}_2(\mathbb{R}) \to \mathbb{R}^\times$ is onto with kernel $\mathrm{SL}_2(\mathbb{R})$. So $\mathrm{SL}_2(\mathbb{R})$ is normal and $\mathrm{GL}_2(\mathbb{R})/\mathrm{SL}_2(\mathbb{R}) \cong \mathbb{R}^\times$. The map $(\mathbb{R}, +) \to \mathbb{C}^\times$, $x \mapsto e^{2\pi i x}$, has range the unit circle $S^1$ and kernel $\mathbb{Z}$. So $\mathbb{R}/\mathbb{Z} \cong S^1$.

**Example ($S_3$ modulo $A_3$ and $D_4$ modulo its center).** The subgroup $A_3$ has index $2$ in $S_3$, so it is normal, and $S_3/A_3$ has two elements: $A_3$ and the set of transpositions. It is isomorphic to $\mathbb{Z}/2$. In $D_4$ the center is $Z = \{1, r^2\}$, by an exercise of Chapter 2. The quotient $D_4/Z$ has $4$ elements, the classes of $1, r, s, s r$. Each one squares to the unit: $r^2 \in Z$, $s^2 = 1$ and $(s r)^2 = 1$. A group of order $4$ in which $x^2 = 1$ for each $x$ is the Klein four group, so $D_4/Z \cong \mathbb{Z}/2 \times \mathbb{Z}/2$.

**Counterexample (The product of cosets needs normality).** Let $H = \{e, (1\,2)\} \le S_3$, with the left coset $(1\,3) H = \{(1\,3), (1\,2\,3)\}$ of Chapter 4. With the representative $(1\,3)$, the rule gives $(1\,3)(1\,3) H = H$. With the representative $(1\,2\,3)$ of the first factor, it gives $(1\,2\,3)(1\,3) H$. The product $(1\,2\,3)(1\,3)$ fixes $1$ and exchanges $2$ and $3$, so it is $(2\,3)$, and $(2\,3) H \neq H$. So the rule is not well defined, and $H$ is not normal: $(1\,3)(1\,2)(1\,3)^{-1} = (2\,3) \notin H$.

**Counterexample (Normality is not transitive).** In $D_4$, let $K = \{1, s, r^2, s r^2\}$ and $N = \{1, s\}$. Then $N \trianglelefteq K$ and $K \trianglelefteq D_4$, because each has index $2$. But $N$ is not normal in $D_4$: $r s r^{-1} = s r^{-2} = s r^2 \notin N$.

**Example (Normal subgroups in Lean).**

<?lean MathlibHandbook/V05/C05/Examples.lean#normal?>

**Example (Kernels in Lean).**

<?lean MathlibHandbook/V05/C05/Examples.lean#ker_normal?>

**Example (The quotient map respects products).**

<?lean MathlibHandbook/V05/C05/Examples.lean#mk_mul?>

**Example (Equal classes).**

<?lean MathlibHandbook/V05/C05/Examples.lean#eq?>

**Example (The universal property).**

<?lean MathlibHandbook/V05/C05/Examples.lean#lift?>

**Example (The first isomorphism theorem in Lean).**

<?lean MathlibHandbook/V05/C05/Examples.lean#first_iso?>

### The library around it

The basic quotient theory is in `Mathlib.GroupTheory.QuotientGroup.Defs`, and the isomorphism theorems are in `Mathlib.GroupTheory.QuotientGroup.Basic`. The lemma `QuotientGroup.ker_mk'` says that the kernel of the quotient map is `N`. The normal subgroups of `G` have their own lattice operations; the largest normal subgroup in `H` is `Subgroup.normalCore`. The commutator subgroup, the smallest normal subgroup with a commutative quotient, is `commutator G`. A group with no normal subgroups other than `⊥` and `⊤` is simple, the class `IsSimpleGroup`.

The notation `G ⧸ N` is not special to groups. It comes from the class `HasQuotient` of `Mathlib.Algebra.Quotient`, whose instances also give the quotient modules `M ⧸ N` and the quotient rings `R ⧸ I`. The notation unfolds to `HasQuotient.Quotient`.

The class `IsSimpleGroup` is in `Mathlib.GroupTheory.Subgroup.Simple`. Its constructor `IsSimpleGroup.mk` asks for a nontrivial group whose only normal subgroups are `⊥` and `⊤`, and `isSimpleGroup_iff` restates this. Simplicity passes along isomorphisms (`MulEquiv.isSimpleGroup_congr`) and to nontrivial quotients (`IsSimpleGroup.isSimpleGroup_of_surjective`). For a subgroup $H$, `Subgroup.isSimpleGroup_iff` describes the simplicity of `↥H` by subgroups of $G$ inside $H$. The module `Mathlib.GroupTheory.QuotientGroup.Simple` connects simplicity with maximal normal subgroups. If $M$ is a normal subgroup that is a coatom of the lattice of subgroups, then $G/M$ is simple, by `Group.isSimpleGroup_of_isCoatom`; for a commutative group the converse holds, by `CommGroup.isSimpleGroup_iff_isCoatom`. The proof is the correspondence theorem of the next section: the normal subgroups of $G/M$ match the normal subgroups between $M$ and $G$.

The module `Mathlib.GroupTheory.QuotientGroup.Finite` deduces finiteness from a subgroup and its quotient. A group $G$ is finite if and only if $H$ and $G/H$ are finite (`finite_iff_subgroup_quotient`). The definitions `Group.fintypeOfKerOfCodom` and `Group.fintypeOfKerLeRange` build a `Fintype` instance from an exact sequence of finite groups. The module `Mathlib.GroupTheory.QuotientGroup.ModEq` links the quotient by $\langle p \rangle$ with congruence modulo $p$ in a commutative additive group: $a \equiv b \pmod p$ if and only if $a$ and $b$ have the same image in $G/\langle p \rangle$, by `AddCommGroup.modEq_iff_eq_mod_zmultiples`. The module `Mathlib.GroupTheory.Subgroup.Saturated` defines a saturated submonoid, `Submonoid.PowSaturated`: if $g^n \in H$ with $n \ne 0$, then $g \in H$. For a subgroup, `Subgroup.saturated_iff_zpow` states this with integer powers. A normal subgroup $N$ is saturated exactly when $G/N$ has no torsion.

Common errors of a learner:

- The quotient `G ⧸ N` has a group instance only with `[N.Normal]`. If instance search fails, the error message speaks of a missing `Group (G ⧸ N)`, not of normality.
- The isomorphism theorems are `≃*`, so they are data. A statement like `Nat.card (G ⧸ f.ker) = Nat.card f.range` follows with `Nat.card_congr (...).toEquiv`.
- The coercion `(a : G ⧸ N)` hides `QuotientGroup.mk`. A rewrite with `QuotientGroup.eq` needs the goal in this form.

### Exercises

1. (A) Explain why `G ⧸ N` needs the instance `N.Normal` to be a group.
2. (A) Give the kernel of the quotient map $G \to G / N$.
3. (A) Show that $\{1, r^2\}$ is normal in $D_4$ and that $\{1, s\}$ is not.
4. (B) Show that $G / N$ is commutative if and only if $a b a^{-1} b^{-1} \in N$ for all $a$ and $b$.
5. (B) Show that $\mathbb{C}^\times / S^1 \cong \mathbb{R}_{>0}$ and $\mathbb{C}^\times / \mathbb{R}_{>0} \cong S^1$. Hint: use $z \mapsto |z|$ and $z \mapsto z / |z|$.
6. (B) Show that $G / Z(G)$ cyclic implies that $G$ is commutative. Hint: write $a = g^i z$ and $b = g^j z'$ with $z, z' \in Z(G)$.
7. (C) Show that the intersection of all the conjugates $g H g^{-1}$ of a subgroup $H$ is the largest normal subgroup of $G$ inside $H$.
8. (L) Prove that the class of $1$ is the unit of `G ⧸ N`. The solution is `mk_one_example`.
9. (L) Prove that the kernel of `QuotientGroup.mk' N` is $N$. The solution is `ker_mk_example`.
10. (L) Prove that $g^{-1} \cdot n \cdot g \in N$ for $n \in N$. The solution is `conj_mem_example`.

### Notes and history

Galois found the normal subgroups in 1832, in his letter to Chevalier, as the subgroups whose left and right cosets agree. He saw that an equation is solvable by radicals when its group has a chain of such subgroups with quotients of prime order. Jordan made the quotient group explicit in his Traité of 1870, and Hölder defined the quotient group of an abstract group in 1889. The first isomorphism theorem in the form above is due to Noether, who stated the three isomorphism theorems for modules and groups in 1927.

In Mathlib, `Subgroup.Normal` is a class so that `G ⧸ N` can be a group by instance search. The price is that a normal subgroup built inside a proof needs `haveI` to become an instance.

### Reference

<?reference?>
