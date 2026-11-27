---
title: Automorphisms, fixed fields and Galois extensions
kind: theory
modules:
  - Mathlib.FieldTheory.Fixed
  - Mathlib.FieldTheory.Galois.Basic
  - Mathlib.FieldTheory.Galois.GaloisClosure
  - Mathlib.FieldTheory.Galois.IsGaloisGroup
  - Mathlib.FieldTheory.Galois.Notation
  - Mathlib.RingTheory.IsGaloisGroup.Defs
  - Mathlib.RingTheory.IsGaloisGroup.Basic
explains:
  E3: [IsGalois, IsGalois.tfae, IsGalois.card_aut_eq_finrank, FixedPoints.finrank_eq_card, IsGaloisGroup]
  E2: [IsGalois.of_card_aut_eq_finrank, IsGalois.of_separable_splitting_field, IsGalois.is_separable_splitting_field, IsGalois.of_fixedField_eq_bot, IsGalois.to_normal, IsGalois.to_isSeparable, IsGalois.self, IsGalois.tower_top_of_isGalois, IsGalois.mem_range_algebraMap_iff_fixed, IsGalois.normalClosure, IsGalois.sup_right, FixedPoints.subfield, FixedPoints.finrank_le_card, FixedPoints.isSeparable, FixedPoints.normal, FixedPoints.minpoly, FixedPoints.toAlgAut_surjective, FiniteGaloisIntermediateField, IsGaloisGroup.of_isGalois, IsGaloisGroup.isGalois]
  E1: auto
families: []
requires: [V11.C04, V05.C06, V07.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Automorphisms, fixed fields and Galois extensions

### Overview

Section 1 showed that a normal extension has enough automorphisms to move each element to each of its conjugates. Separability (Chapter 4) makes the conjugates distinct. An extension that is both normal and separable is a Galois extension, and for a finite Galois extension $L/K$ the group $\operatorname{Aut}(L/K)$ has exactly $[L:K]$ elements. This section proves that equality and its converse.

The main tool goes from groups to fields. For a finite group $G$ of automorphisms of a field $L$, the theorem of Artin says that $[L : L^G] = |G|$ and that $L/L^G$ is Galois, where $L^G$ is the fixed field. The proof uses the independence of characters of Dedekind. With it, four conditions on a finite extension become equivalent; these are the items of `IsGalois.tfae`.

The section uses group actions (Volume 5, Chapter 6), linear independence and dimension (Volume 7, Chapter 2), the embeddings of an extension into an algebraic closure and the separable degree (Chapter 4), and Section 1.

### Definitions

**Definition (Automorphism group).** Let $L/K$ be an extension. The group $\operatorname{Aut}(L/K)$ is the set of the field automorphisms $\sigma : L \to L$ with $\sigma(a) = a$ for all $a \in K$, with composition as the product. For a Galois extension it is written $\operatorname{Gal}(L/K)$, the Galois group.

In Mathlib the group is the type `L ≃ₐ[K] L` of the $K$-algebra equivalences, and the notation `Gal(L/K)` from `Mathlib.FieldTheory.Galois.Notation` stands for it, for all extensions and not only Galois ones.

**Definition (Fixed field).** Let $G$ be a group that acts on a field $L$ by ring automorphisms. The fixed field is $L^G = \{x \in L : \sigma(x) = x \text{ for all } \sigma \in G\}$. It is a subfield of $L$, since each $\sigma$ respects sums, products and inverses.

::: mathlib
`FixedPoints.subfield` · `Mathlib.FieldTheory.Fixed`

`FixedPoints.subfield G F` is the subfield of the fixed points of an action `[MulSemiringAction G F]`. For a subgroup `H` of `Gal(E/F)` the version as an intermediate field is `IntermediateField.fixedField H`, which Section 3 uses.

<?decl FixedPoints.subfield?>
:::

**Definition (Galois extension).** An extension $L/K$ is Galois if it is normal and separable.

::: mathlib
`IsGalois` · `Mathlib.FieldTheory.Galois.Basic`

The class `IsGalois F E` has the two fields `IsGalois.to_isSeparable` and `IsGalois.to_normal`. It does not ask for finite dimension; most theorems below add `[FiniteDimensional F E]`. The instance `IsGalois.self` says that `F/F` is Galois.

<?decl IsGalois?>
:::

### Theorems and proofs

**Theorem (Dedekind).** Let $M$ be a monoid and $L$ a field. Distinct monoid homomorphisms $\chi_1, \dots, \chi_n : M \to L$ (with the multiplication of $L$) are linearly independent over $L$ as functions $M \to L$.

*Proof.* Suppose not, and choose a relation $\sum_{i} a_i \chi_i = 0$ with the smallest number of nonzero coefficients. Renumber so that the relation is $a_1 \chi_1 + \dots + a_r \chi_r = 0$ with all $a_i \neq 0$. Then $r \geq 2$, since $\chi_1(1) = 1$ excludes $a_1 \chi_1 = 0$. Since $\chi_1 \neq \chi_2$, there is $h \in M$ with $\chi_1(h) \neq \chi_2(h)$. For each $g \in M$, the relation at $hg$ gives $\sum_i a_i \chi_i(h) \chi_i(g) = 0$, and the relation at $g$ times $\chi_1(h)$ gives $\sum_i a_i \chi_1(h) \chi_i(g) = 0$. Subtract:
$$\sum_{i=2}^r a_i \big(\chi_i(h) - \chi_1(h)\big) \chi_i(g) = 0.$$
This is a relation with at most $r - 1$ nonzero coefficients, and the coefficient of $\chi_2$ is not zero. This contradicts the choice of $r$. $\square$

The automorphisms $\sigma_1, \dots, \sigma_n$ of a field $L$ are such homomorphisms on the monoid $L^\times$. So distinct automorphisms of $L$ are linearly independent over $L$.

::: mathlib
`linearIndependent_monoidHom` · `Mathlib.LinearAlgebra.LinearIndependent.Basic`

The statement is `LinearIndependent L (fun f : G →* L ↦ (f : G → L))` for a monoid `G` and a domain `L`.

<?decl linearIndependent_monoidHom?>
:::

**Theorem (Artin).** Let $G$ be a finite group that acts faithfully on a field $L$ by ring automorphisms, and $K = L^G$. Then $[L : K] = |G|$, and $L/K$ is a Galois extension.

*Proof.* Let $G = \{\sigma_1, \dots, \sigma_n\}$ with $\sigma_1 = 1$. Faithful means that distinct elements of $G$ act by distinct maps.

First, $[L : K] \leq n$. Let $\alpha_1, \dots, \alpha_m \in L$ with $m > n$. The linear system
$$\sum_{j=1}^m \sigma_i(\alpha_j)\, x_j = 0 \qquad (i = 1, \dots, n)$$
has $n$ equations and $m > n$ unknowns, so it has a nonzero solution in $L^m$. Choose one with the fewest nonzero entries, scaled so that $x_1 = 1$. Let $\tau \in G$. Apply $\tau$ to the equations: $\sum_j \tau\sigma_i(\alpha_j)\, \tau(x_j) = 0$. As $i$ runs from $1$ to $n$, $\tau\sigma_i$ runs through $G$, so $(\tau(x_j))_j$ is again a solution. The difference $(x_j - \tau(x_j))_j$ is a solution with fewer nonzero entries, so it is zero. So $\tau(x_j) = x_j$ for all $\tau$, and each $x_j \in K$. The equation with $\sigma_1 = 1$ reads $\sum_j \alpha_j x_j = 0$, a nontrivial relation over $K$.

Second, $[L : K] \geq n$. Suppose $[L : K] = d < n$, with a basis $\beta_1, \dots, \beta_d$. The system $\sum_{i=1}^n y_i\, \sigma_i(\beta_k) = 0$ for $k = 1, \dots, d$ has $d < n$ equations, so it has a nonzero solution $y \in L^n$. The map $\phi = \sum_i y_i \sigma_i : L \to L$ is $K$-linear, because each $\sigma_i$ fixes $K$, and it is zero on the basis. So $\phi = 0$, which contradicts the theorem of Dedekind.

Third, $L/K$ is Galois. Let $\alpha \in L$, and let $\alpha = \alpha_1, \dots, \alpha_r$ be the distinct elements of its orbit under $G$. Put $f = \prod_{k=1}^r (X - \alpha_k)$. Each $\tau \in G$ permutes the orbit, so it fixes the coefficients of $f$, and $f \in K[X]$. The minimal polynomial of $\alpha$ over $K$ divides $f$, which has distinct roots and splits in $L$. So $\alpha$ is separable over $K$, and its minimal polynomial splits in $L$. Since $[L:K]$ is finite, $L/K$ is algebraic, so it is separable and normal. $\square$

::: mathlib
`FixedPoints.finrank_eq_card` · `Mathlib.FieldTheory.Fixed`

The statement is `Module.finrank (FixedPoints.subfield G F) F = Fintype.card G` for a finite group `G` with `[MulSemiringAction G F]` and `[FaithfulSMul G F]`. The inequality, `FixedPoints.finrank_le_card`, holds without faithfulness. The instances `FixedPoints.isSeparable` and `FixedPoints.normal` give the Galois property, and `FixedPoints.minpoly`, the minimal polynomial over the fixed field, is the product over the orbit. `FixedPoints.toAlgAut_surjective` says that each automorphism of `F` over the fixed field comes from `G`.

<?decl FixedPoints.finrank_eq_card?>
:::

**Lemma (Bound).** Let $L/K$ be finite. Then $|\operatorname{Aut}(L/K)| \leq [L:K]$, with equality if and only if $L/K$ is Galois.

*Proof.* Let $\Omega$ be an algebraic closure of $L$. Each $\sigma \in \operatorname{Aut}(L/K)$ gives a $K$-embedding $L \to \Omega$, and distinct automorphisms give distinct embeddings. By Chapter 4, Section 2, the number of $K$-embeddings $L \to \Omega$ is the separable degree $[L:K]_s \leq [L:K]$, with equality if and only if $L/K$ is separable. So $|\operatorname{Aut}(L/K)| \leq [L:K]_s \leq [L:K]$.

If $L/K$ is Galois, it is normal, so each $K$-embedding $L \to \Omega$ has the image $L$ (Section 1) and comes from an automorphism. So $|\operatorname{Aut}(L/K)| = [L:K]_s = [L:K]$. Conversely, if $|\operatorname{Aut}(L/K)| = [L:K]$, put $G = \operatorname{Aut}(L/K)$ and $F = L^G \supseteq K$. By Artin, $[L:F] = |G| = [L:K]$, so $F = K$ by the tower law, and $L/K = L/L^G$ is Galois by Artin. $\square$

**Corollary (All the automorphisms).** In the situation of Artin's theorem, $\operatorname{Aut}(L/L^G) = G$.

*Proof.* The group $G$ is a subgroup of $\operatorname{Aut}(L/K)$ with $K = L^G$. By the lemma, $|\operatorname{Aut}(L/K)| \leq [L:K] = |G|$. So the two groups are equal. $\square$

**Theorem (Characterizations).** For a finite extension $L/K$ these conditions are equivalent.

1. $L/K$ is Galois.
2. The fixed field of $\operatorname{Aut}(L/K)$ is $K$.
3. $|\operatorname{Aut}(L/K)| = [L:K]$.
4. $L$ is the splitting field over $K$ of a separable polynomial.

*Proof.* The lemma gives 1 if and only if 3.

3 implies 2 is in the proof of the lemma, and 2 implies 1 is Artin's theorem.

1 implies 4: let $f$ be the product of the distinct minimal polynomials of a basis of $L$ over $K$. They are separable, split in $L$ and have no common root, so $f$ is separable, and its roots generate $L$.

4 implies 1: a splitting field is normal (Section 1). The roots of a separable polynomial are separable elements, and the separable elements of $L$ form a subfield (Chapter 4, Section 2). That subfield contains $K$ and the roots, so it is $L$. $\square$

::: mathlib
`IsGalois.tfae` · `Mathlib.FieldTheory.Galois.Basic`

The statement is `List.TFAE [IsGalois F E, fixedField ⊤ = ⊥, Nat.card Gal(E/F) = finrank F E, ∃ p, p.Separable ∧ IsSplittingField F E p]` under `[FiniteDimensional F E]`. Here `⊤` is the whole group and `⊥` is the smallest intermediate field, the image of `F`. The single directions have their own names: `IsGalois.of_fixedField_eq_bot`, `IsGalois.of_card_aut_eq_finrank`, `IsGalois.of_separable_splitting_field` and `IsGalois.is_separable_splitting_field`.

<?decl IsGalois.tfae?>
:::

::: mathlib
`IsGalois.card_aut_eq_finrank` · `Mathlib.FieldTheory.Galois.Basic`

The equation `Nat.card Gal(E/F) = Module.finrank F E` for a finite Galois extension. A consequence is `IsGalois.mem_range_algebraMap_iff_fixed`: an element of `E` lies in `F` if and only if each automorphism fixes it.

<?decl IsGalois.card_aut_eq_finrank?>
:::

**Corollary (Towers).** If $L/K$ is Galois and $K \subseteq M \subseteq L$, then $L/M$ is Galois.

*Proof.* $L/M$ is normal by Section 1 and separable by Chapter 4, Section 1. $\square$

Mathlib has this as `IsGalois.tower_top_of_isGalois`; $M/K$ need not be Galois. The normal closure of a finite separable extension is Galois (`IsGalois.normalClosure`). The type `FiniteGaloisIntermediateField k K` collects the finite Galois subextensions, for use in Section 3.

**Definition (Galois group of an action).** A group $G$ that acts on $L$ by $K$-algebra automorphisms is a Galois group for $L/K$ if the action is faithful and the fixed points are exactly $K$.

::: mathlib
`IsGaloisGroup` · `Mathlib.RingTheory.IsGaloisGroup.Defs`

The class `IsGaloisGroup G A B` is for an action of `G` on a ring `B` over `A`. It does not ask that `B` be a field, so it fits rings of integers too. For fields, `IsGaloisGroup.of_isGalois` says that `Gal(L/K)` is a Galois group of a Galois extension, and `IsGaloisGroup.isGalois` says that a finite Galois group makes `L/K` Galois.

<?decl IsGaloisGroup?>
:::

### Examples

**Example (The biquadratic field).** Let $L = \mathbb{Q}(\sqrt 2, \sqrt 3)$, of degree $4$ (Chapter 1). It is the splitting field of $(X^2 - 2)(X^2 - 3)$, which has the four distinct roots $\pm\sqrt 2, \pm\sqrt 3$. So $L/\mathbb{Q}$ is Galois and $|\operatorname{Gal}(L/\mathbb{Q})| = 4$. An automorphism is fixed by the signs of $\sigma(\sqrt 2) = \pm\sqrt 2$ and $\sigma(\sqrt 3) = \pm\sqrt 3$, and all four choices occur. With $\sigma$ changing the sign of $\sqrt 2$ only and $\tau$ that of $\sqrt 3$ only, the group is $\{1, \sigma, \tau, \sigma\tau\} \cong (\mathbb{Z}/2)^2$. For condition 2: an element $a + b\sqrt 2 + c\sqrt 3 + d\sqrt 6$ is fixed by $\sigma$ if and only if $b = d = 0$, and then by $\tau$ if and only if $c = 0$. So the fixed field is $\mathbb{Q}$.

**Example (Too few automorphisms).** Let $L = \mathbb{Q}(\sqrt[3]{2})$. Section 1 showed that $\operatorname{Aut}(L/\mathbb{Q}) = 1$. Its fixed field is $L$, not $\mathbb{Q}$, and $1 < 3 = [L:\mathbb{Q}]$. The extension is separable but not normal. In characteristic $p$, the extension $\mathbb{F}_p(s)/\mathbb{F}_p(s^p)$ is normal but not separable, and its automorphism group is again trivial, with degree $p$. So each of the two conditions in the definition of a Galois extension is needed for $|\operatorname{Aut}(L/K)| = [L:K]$.

### The library around it

The file `Mathlib.FieldTheory.Fixed` holds Artin's theorem. The file `Mathlib.FieldTheory.Galois.Basic` holds the class `IsGalois`, the characterizations, and the fundamental theorem of Section 3. The files on `IsGaloisGroup` give the theory for an abstract action. The theorem `IsGalois.sup_right` says that a Galois extension stays Galois after a base change inside a common field. The reference table lists the declarations of the section.

### Exercises

1. (A) Find $\operatorname{Gal}(\mathbb{Q}(i, \sqrt 2)/\mathbb{Q})$ and its fixed field.
2. (A) Show that each extension of degree $2$ in characteristic other than $2$ is Galois, and give an extension of degree $2$ in characteristic $2$ that is not Galois. Hint: $\mathbb{F}_2(s)/\mathbb{F}_2(s^2)$.
3. (A) Let $L/K$ be finite Galois with group $G$, and $\alpha \in L$. Show that $\prod_{\sigma \in G} (X - \sigma(\alpha))$ is a power of the minimal polynomial of $\alpha$.
4. (B) Show that $\mathbb{Q}(\sqrt[4]{2}, i)$ is Galois over $\mathbb{Q}$ of degree $8$, and list the images of $\sqrt[4]{2}$ and $i$ under its eight automorphisms.
5. (B) Let $L = K(x_1, \dots, x_n)$ be a field of rational functions and $S_n$ act by permuting the variables. Show that $[L : L^{S_n}] = n!$ and that $L^{S_n}$ contains the elementary symmetric polynomials $e_1, \dots, e_n$. Deduce that $L^{S_n} = K(e_1, \dots, e_n)$. Hint: $L$ splits $\prod (X - x_i)$.
6. (B) Let $L/K$ be finite and $H$ a finite group of automorphisms of $L$ with $L^H = K$. Show that $H = \operatorname{Aut}(L/K)$.
7. (C) Let $L/K$ be finite Galois with group $G$ and $K$ infinite. Show that there is $\alpha \in L$ such that $(\sigma(\alpha))_{\sigma \in G}$ is a basis of $L$ over $K$. Mathlib proves this for all $K$ as `IsGalois.normalBasis`.

### Notes and history

Dedekind proved the independence of characters. Emil Artin made it the central tool of Galois theory in his lectures, published as "Galois Theory" (Notre Dame, 1942). His proof of $[L : L^G] = |G|$ by the linear system is the one given here. The theorem on the fixed field of $S_n$ in Exercise 5 is the field form of the fundamental theorem on symmetric polynomials.

### Reference

<?reference?>
