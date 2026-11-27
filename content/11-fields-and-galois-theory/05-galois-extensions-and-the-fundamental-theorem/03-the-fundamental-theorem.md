---
title: The fundamental theorem of Galois theory
kind: theory
modules:
  - Mathlib.FieldTheory.Galois.Basic
  - Mathlib.FieldTheory.Galois.Infinite
  - Mathlib.FieldTheory.KrullTopology
  - Mathlib.FieldTheory.AbsoluteGaloisGroup
  - Mathlib.FieldTheory.Galois.Profinite
  - Mathlib.FieldTheory.Galois.NormalBasis
  - Mathlib.FieldTheory.Galois.Sylow
explains:
  E3: [IsGalois.intermediateFieldEquivSubgroup, IntermediateField.fixedField, IntermediateField.fixingSubgroup, IsGalois.normalAutEquivQuotient, krullTopology, InfiniteGalois.IntermediateFieldEquivClosedSubgroup]
  E2: [IsGalois.fixedField_fixingSubgroup, IntermediateField.fixingSubgroup_fixedField, IsGalois.card_fixingSubgroup_eq_finrank, IntermediateField.finrank_fixedField_eq_card, IntermediateField.fixingSubgroupEquiv, IsGalois.galoisInsertionIntermediateFieldSubgroup, IsGalois.of_fixedField_normal_subgroup, IsGalois.fixingSubgroup_normal_of_isGalois, IntermediateField.fixingSubgroup_isOpen, InfiniteGalois.normalAutEquivQuotient, Field.absoluteGaloisGroup, InfiniteGalois.profiniteGalGrp, IsGalois.normalBasis, IsGalois.exists_intermediateField_finrank_pow_prime]
  E1: auto
families: []
requires: [V11.C04, V05.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The fundamental theorem of Galois theory

### Overview

Let $L/K$ be a finite Galois extension with group $G$. An intermediate field $M$ gives the subgroup of the automorphisms that fix $M$, and a subgroup $H$ gives the field of the elements that $H$ fixes. The fundamental theorem says that these maps are inverse bijections, that they reverse inclusions, and that they convert degrees into indices. Under the bijection, the intermediate fields that are Galois over $K$ correspond to the normal subgroups, and the quotient group is the Galois group of the smaller extension.

So the lattice of the intermediate fields is the lattice of the subgroups of a finite group turned upside down. This section proves the theorem from the results of Sections 1 and 2, computes the two lattices for $\mathbb{Q}(\sqrt 2, \sqrt 3)$ and for the splitting field of $X^3 - 2$, and states the version for infinite Galois extensions, where the group carries the Krull topology and only the closed subgroups occur.

The section uses subgroups, normal subgroups and the first isomorphism theorem (Volume 5, Chapters 3 and 5), Sections 1 and 2, and the tower law (Chapter 1).

### Definitions

**Definition (Fixing subgroup).** Let $L/K$ be an extension and $M$ an intermediate field. The fixing subgroup of $M$ is
$$\operatorname{Fix}(M) = \{\sigma \in \operatorname{Aut}(L/K) : \sigma(x) = x \text{ for all } x \in M\}.$$
It is a subgroup of $\operatorname{Aut}(L/K)$, and it is the same group as $\operatorname{Aut}(L/M)$.

**Definition (Fixed field of a subgroup).** For a subgroup $H$ of $\operatorname{Aut}(L/K)$, the fixed field $L^H$ is the set of the $x \in L$ with $\sigma(x) = x$ for all $\sigma \in H$. It is an intermediate field of $L/K$.

Both maps reverse inclusions: if $M \subseteq M'$ then $\operatorname{Fix}(M') \subseteq \operatorname{Fix}(M)$, and if $H \subseteq H'$ then $L^{H'} \subseteq L^H$. Also $M \subseteq L^{\operatorname{Fix}(M)}$ and $H \subseteq \operatorname{Fix}(L^H)$, by the definitions.

::: mathlib
`IntermediateField.fixingSubgroup` · `Mathlib.FieldTheory.Galois.Basic`

`K.fixingSubgroup` is a `Subgroup Gal(E/F)` for an intermediate field `K : IntermediateField F E`. The isomorphism `IntermediateField.fixingSubgroupEquiv K` identifies it with `Gal(E/K)`, the group of the automorphisms over the larger base `K`. The two are different types in Lean.

<?decl IntermediateField.fixingSubgroup?>
:::

::: mathlib
`IntermediateField.fixedField` · `Mathlib.FieldTheory.Galois.Basic`

`IntermediateField.fixedField H` is the intermediate field of the elements of `E` that each `σ ∈ H` fixes, for `H : Subgroup Gal(E/F)`. Unlike `FixedPoints.subfield` of Section 2, it is an intermediate field over `F`.

<?decl IntermediateField.fixedField?>
:::

### Theorems and proofs

**Theorem (Fundamental theorem of Galois theory).** Let $L/K$ be a finite Galois extension with group $G = \operatorname{Gal}(L/K)$.

1. The maps $M \mapsto \operatorname{Fix}(M)$ and $H \mapsto L^H$ are inverse bijections between the intermediate fields of $L/K$ and the subgroups of $G$, and they reverse inclusions.
2. For each intermediate field $M$, $[L : M] = |\operatorname{Fix}(M)|$ and $[M : K] = [G : \operatorname{Fix}(M)]$.
3. For $\sigma \in G$, $\operatorname{Fix}(\sigma(M)) = \sigma \operatorname{Fix}(M) \sigma^{-1}$.
4. $M/K$ is Galois if and only if $\operatorname{Fix}(M)$ is a normal subgroup of $G$. In that case restriction gives an isomorphism $G / \operatorname{Fix}(M) \cong \operatorname{Gal}(M/K)$.

*Proof.* Part 1. Let $M$ be an intermediate field. By Section 2, $L/M$ is Galois, and $\operatorname{Fix}(M) = \operatorname{Aut}(L/M)$. By the characterizations of Section 2 (condition 2), the fixed field of $\operatorname{Aut}(L/M)$ is $M$. So $L^{\operatorname{Fix}(M)} = M$. Let $H$ be a subgroup of $G$. It is finite and acts faithfully on $L$. By Artin's theorem and its corollary in Section 2, $\operatorname{Aut}(L / L^H) = H$, that is, $\operatorname{Fix}(L^H) = H$. So the two maps are inverse to each other.

Part 2. Since $L/M$ is Galois, $|\operatorname{Fix}(M)| = |\operatorname{Aut}(L/M)| = [L:M]$ by Section 2. The tower law and Lagrange's theorem give
$$[M:K] = \frac{[L:K]}{[L:M]} = \frac{|G|}{|\operatorname{Fix}(M)|} = [G : \operatorname{Fix}(M)].$$

Part 3. For $\tau \in G$: $\tau$ fixes $\sigma(M)$ pointwise if and only if $\tau\sigma(x) = \sigma(x)$ for all $x \in M$, if and only if $\sigma^{-1}\tau\sigma \in \operatorname{Fix}(M)$, if and only if $\tau \in \sigma \operatorname{Fix}(M) \sigma^{-1}$.

Part 4. First, $M/K$ is Galois if and only if $\sigma(M) = M$ for all $\sigma \in G$. Since $M/K$ is separable, only normality is in question. If $M/K$ is normal, each $\sigma|_M$ is a $K$-embedding of $M$ into $L$, so $\sigma(M) = M$ by Section 1. Conversely, assume $\sigma(M) = M$ for all $\sigma$. Let $\alpha \in M$ with minimal polynomial $m$ over $K$. Since $L/K$ is normal, $m$ splits in $L$, and by the theorem on conjugates in Section 1 its roots are the $\sigma(\alpha)$ with $\sigma \in G$. These lie in $\sigma(M) = M$, so $m$ splits in $M$.

By Part 1 and Part 3, $\sigma(M) = M$ if and only if $\sigma \operatorname{Fix}(M) \sigma^{-1} = \operatorname{Fix}(M)$. So $M/K$ is Galois if and only if $\operatorname{Fix}(M)$ is normal in $G$.

In that case, Section 1 gives the restriction homomorphism $r : G \to \operatorname{Gal}(M/K)$, $\sigma \mapsto \sigma|_M$, and it is surjective. Its kernel is $\operatorname{Fix}(M)$. The first isomorphism theorem (Volume 5, Chapter 5) gives $G/\operatorname{Fix}(M) \cong \operatorname{Gal}(M/K)$. $\square$

::: mathlib
`IsGalois.intermediateFieldEquivSubgroup` · `Mathlib.FieldTheory.Galois.Basic`

The correspondence as an order isomorphism `IntermediateField F E ≃o (Subgroup Gal(E/F))ᵒᵈ` under `[FiniteDimensional F E] [IsGalois F E]`. The two halves of Part 1 are `IsGalois.fixedField_fixingSubgroup` and `IntermediateField.fixingSubgroup_fixedField`. Part 2 is `IsGalois.card_fixingSubgroup_eq_finrank` and `IntermediateField.finrank_fixedField_eq_card`. The structure `IsGalois.galoisInsertionIntermediateFieldSubgroup` records the weaker fact, true without the Galois hypothesis, that the two maps form a Galois insertion.

<?decl IsGalois.intermediateFieldEquivSubgroup?>
:::

::: mathlib
`IsGalois.normalAutEquivQuotient` · `Mathlib.FieldTheory.Galois.Basic`

For a normal subgroup `H` of `Gal(L/K)`, the isomorphism `Gal(L/K) ⧸ H ≃* Gal(fixedField H/K)`. The instance `IsGalois.of_fixedField_normal_subgroup` says that the fixed field of a normal subgroup is Galois, and `IsGalois.fixingSubgroup_normal_of_isGalois` gives the other direction of Part 4.

<?decl IsGalois.normalAutEquivQuotient?>
:::

**Corollary (Finitely many intermediate fields).** A finite Galois extension has only finitely many intermediate fields.

*Proof.* A finite group has finitely many subgroups. $\square$

With the theorem of Steinitz (Chapter 4, Section 3) this gives a second proof of the primitive element theorem for finite separable extensions: embed the extension in its Galois closure.

**Corollary (Sylow subfields).** Let $L/K$ be finite Galois, and let $p^n$ divide $[L:K]$ for a prime $p$. Then there is an intermediate field $N$ with $[L:N] = p^n$.

*Proof.* By the Sylow theorems (Volume 5, Chapter 8), $G$ has a subgroup $H$ of order $p^n$. Put $N = L^H$, so $[L:N] = |H|$. $\square$

Mathlib has this as `IsGalois.exists_intermediateField_finrank_pow_prime`, in `Mathlib.FieldTheory.Galois.Sylow`.

**Theorem (Normal basis).** Let $L/K$ be finite Galois with group $G$. There is $\alpha \in L$ such that $(\sigma(\alpha))_{\sigma \in G}$ is a basis of $L$ over $K$.

This section does not prove it. Exercise 7 of Section 2 treats the case of an infinite $K$; Mathlib has the general case as `IsGalois.normalBasis`, a basis indexed by `Gal(L/K)`.

**Theorem (Infinite Galois theory).** Let $L/K$ be a Galois extension, possibly infinite. Give $G = \operatorname{Gal}(L/K)$ the Krull topology, in which the subgroups $\operatorname{Fix}(E)$ for finite intermediate extensions $E/K$ form a basis of neighbourhoods of $1$. Then $G$ is a profinite group, and $M \mapsto \operatorname{Fix}(M)$ is a bijection from the intermediate fields onto the closed subgroups of $G$. Its inverse is $H \mapsto L^H$, and the open subgroups correspond to the finite subextensions.

The proof uses the finite theorem on each finite Galois subextension and a compactness argument; this section does not give it. A subgroup $H$ that is not closed has the same fixed field as its closure, so the restriction to closed subgroups is needed.

::: mathlib
`krullTopology` · `Mathlib.FieldTheory.KrullTopology`

The instance `krullTopology K L : TopologicalSpace Gal(L/K)` is defined from the filter basis of the groups `Gal(L/E)` for finite `E`. The theorem `IntermediateField.fixingSubgroup_isOpen` says that such a group is open. `InfiniteGalois.profiniteGalGrp` packs the group as a profinite group, and `Field.absoluteGaloisGroup K` is the group of an algebraic closure of `K`.

<?decl krullTopology?>
:::

::: mathlib
`InfiniteGalois.IntermediateFieldEquivClosedSubgroup` · `Mathlib.FieldTheory.Galois.Infinite`

The order isomorphism `IntermediateField k K ≃o (ClosedSubgroup Gal(K/k))ᵒᵈ` for `[IsGalois k K]`, without finite dimension. The quotient part is `InfiniteGalois.normalAutEquivQuotient`, for a closed normal subgroup.

<?decl InfiniteGalois.IntermediateFieldEquivClosedSubgroup?>
:::

### Examples

**Example (The biquadratic field).** Let $L = \mathbb{Q}(\sqrt 2, \sqrt 3)$ with $G = \{1, \sigma, \tau, \sigma\tau\}$ as in Section 2: $\sigma$ changes the sign of $\sqrt 2$, and $\tau$ that of $\sqrt 3$. The group $(\mathbb{Z}/2)^2$ has five subgroups: $1$, $\langle\sigma\rangle$, $\langle\tau\rangle$, $\langle\sigma\tau\rangle$ and $G$. Their fixed fields are $L$, $\mathbb{Q}(\sqrt 3)$, $\mathbb{Q}(\sqrt 2)$, $\mathbb{Q}(\sqrt 6)$ and $\mathbb{Q}$. For $\langle\sigma\tau\rangle$: $\sigma\tau(\sqrt 6) = (-\sqrt 2)(-\sqrt 3) = \sqrt 6$, and the fixed field has degree $[G : \langle\sigma\tau\rangle] = 2$ over $\mathbb{Q}$, so it is $\mathbb{Q}(\sqrt 6)$. So $L$ has exactly three subfields of degree $2$, the five fields of Chapter 4, Section 3. All five fields are Galois over $\mathbb{Q}$, since $G$ is abelian.

**Example (The splitting field of $X^3 - 2$).** Let $a = \sqrt[3]{2}$, $\omega = e^{2\pi i/3}$, and $L = \mathbb{Q}(a, \omega)$, of degree $6$ (Section 1). An automorphism sends $a$ to one of $a, a\omega, a\omega^2$ and $\omega$ to one of $\omega, \omega^2$; each of the six choices occurs. Let $\sigma$ be given by $a \mapsto a\omega$, $\omega \mapsto \omega$, and let $\tau$ be complex conjugation, $a \mapsto a$, $\omega \mapsto \omega^2$. Then $\sigma$ has order $3$, $\tau$ has order $2$, and $\tau\sigma\tau = \sigma^{-1}$, so $G \cong S_3$, acting on the three roots. The subgroups and their fixed fields are:

- $1$ and $L$; $G$ and $\mathbb{Q}$;
- $\langle\sigma\rangle$, of index $2$, and $\mathbb{Q}(\omega)$, since $\sigma$ fixes $\omega$;
- $\langle\tau\rangle$ and $\mathbb{Q}(a)$; $\langle\sigma\tau\rangle$ and $\mathbb{Q}(a\omega^2)$; $\langle\sigma^2\tau\rangle$ and $\mathbb{Q}(a\omega)$.

For the last line: $\sigma\tau(a\omega^2) = \sigma(a\omega) = a\omega^2$, and $\sigma^2\tau(a\omega) = \sigma^2(a\omega^2) = \sigma^2(a)\,\omega^2 = a\omega^4 = a\omega$, using $\sigma^2(a) = a\omega^2$ and $\sigma(\omega) = \omega$. Each fixed field has degree $3$ by Part 2. The only proper nontrivial normal subgroup is $\langle\sigma\rangle$, so $\mathbb{Q}(\omega)$ is the only one of these fields, besides $\mathbb{Q}$ and $L$, that is Galois over $\mathbb{Q}$, and $\operatorname{Gal}(\mathbb{Q}(\omega)/\mathbb{Q}) \cong S_3/A_3 \cong \mathbb{Z}/2$. The three subgroups of order $2$ are conjugate, and Part 3 matches this: their fixed fields $\mathbb{Q}(a)$, $\mathbb{Q}(a\omega)$, $\mathbb{Q}(a\omega^2)$ are images of each other under $\sigma$.

**Example (Without the Galois hypothesis).** Let $L = \mathbb{Q}(a)$ with $a = \sqrt[3]{2}$. Its automorphism group is trivial, with one subgroup. But $L/\mathbb{Q}$ has two intermediate fields, $\mathbb{Q}$ and $L$. The map $M \mapsto \operatorname{Fix}(M)$ sends both to the trivial group, so it is not injective, and the fixed field of the trivial group is $L$, not $\mathbb{Q}$. So the theorem fails for extensions that are not normal. For an infinite extension the topology is needed in the same way: in $\operatorname{Gal}(\overline{\mathbb{F}}_p/\mathbb{F}_p)$, the subgroup generated by the Frobenius automorphism is not closed, and it has the same fixed field $\mathbb{F}_p$ as the whole group (Chapter 7).

### The library around it

The finite theorem is in `Mathlib.FieldTheory.Galois.Basic`. The infinite theorem is in `Mathlib.FieldTheory.Galois.Infinite`, with the topology in `Mathlib.FieldTheory.KrullTopology` and the identification of the group with a limit of finite groups in `Mathlib.FieldTheory.Galois.Profinite`. The absolute Galois group is in `Mathlib.FieldTheory.AbsoluteGaloisGroup`. The normal basis theorem is in `Mathlib.FieldTheory.Galois.NormalBasis`. The reference table lists the declarations of the section.

### Exercises

1. (A) List the intermediate fields of $\mathbb{Q}(\zeta_7)/\mathbb{Q}$, where $\zeta_7 = e^{2\pi i/7}$ and the Galois group is cyclic of order $6$. Hint: there is one field of degree $2$ and one of degree $3$; the field of degree $2$ is $\mathbb{Q}(\sqrt{-7})$.
2. (A) Let $L/K$ be Galois with an abelian group. Show that each intermediate field is Galois over $K$.
3. (A) Let $M_1, M_2$ be intermediate fields of a finite Galois $L/K$. Show that $\operatorname{Fix}(M_1 M_2) = \operatorname{Fix}(M_1) \cap \operatorname{Fix}(M_2)$ and that $L^{\langle H_1, H_2 \rangle} = L^{H_1} \cap L^{H_2}$.
4. (B) Find all intermediate fields of $\mathbb{Q}(\sqrt[4]{2}, i)/\mathbb{Q}$, with Galois group $D_4$ of order $8$. There are ten subgroups, so there are ten fields.
5. (B) Let $L/K$ be finite Galois and $M_1, M_2$ intermediate fields with $M_1/K$ Galois. Show that $M_1 M_2 / M_2$ is Galois and that $\operatorname{Gal}(M_1 M_2 / M_2) \cong \operatorname{Gal}(M_1 / M_1 \cap M_2)$.
6. (B) Show that a Galois extension of degree $p^n$, $p$ prime, has a chain of intermediate fields $K = M_0 \subset M_1 \subset \dots \subset M_n = L$ with each step Galois of degree $p$.
7. (C) Prove the fundamental theorem of algebra: each nonconstant polynomial over $\mathbb{C}$ has a root. Use the Galois closure $L$ of a finite extension of $\mathbb{R}$ that contains $\mathbb{C}$, a Sylow $2$-subgroup of its group, the fact that real polynomials of odd degree have real roots, and Exercise 6.

### Notes and history

Galois described the correspondence between subgroups and the auxiliary equations in his memoir of 1831, which was published by Liouville in 1846. Krull extended the theorem to infinite Galois extensions in 1928, with the topology that carries his name. The proof of the fundamental theorem of algebra in Exercise 7 appears in Artin's lectures.

### Reference

<?reference?>
