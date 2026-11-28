---
title: Infinite places, embeddings and CM fields
kind: api
modules:
  - Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
  - Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
  - Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
  - Mathlib.NumberTheory.NumberField.CMField
explains:
  E2: [NumberField.Embeddings.pow_eq_one_of_norm_le_one, NumberField.Embeddings.range_eval_eq_rootSet_minpoly, NumberField.InfinitePlace.isRamified_iff, NumberField.InfinitePlace.card_stabilizer, NumberField.InfinitePlace.unramifiedPlacesOver_ncard_add_eq_finrank, NumberField.maximalRealSubfield, NumberField.IsCMField.indexRealUnits_eq_one_or_two, NumberField.IsCMField.regulator_div_regulator_eq_two_pow_mul_indexRealUnits_inv]
  E1: auto
families: []
requires: [V11.C02, V11.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Infinite places, embeddings and CM fields

### Overview

Section 2 defined the infinite places of a number field $K$: the absolute values $w(x) = |\sigma(x)|$ that come from an embedding $\sigma : K \to \mathbb{C}$. A real embedding gives one place, and a pair of conjugate complex embeddings gives one place. This section is about the finer structure around that definition. It treats the embeddings themselves and their conjugates, the behaviour of places in an extension $K/k$, the fields with only real or only complex places, and the CM fields.

`Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings` counts the embeddings, proves finiteness results for elements of bounded size, and gives the vocabulary of complex embeddings: conjugation, real embeddings, embeddings over a subfield. `InfinitePlace.Ramification` defines ramified places in an extension and the action of the Galois group on places. `InfinitePlace.TotallyRealComplex` defines totally real and totally complex fields and the maximal real subfield. `Mathlib.NumberTheory.NumberField.CMField` defines CM fields, their complex conjugation and the comparison of their units with those of the maximal real subfield.

### The library around it

#### Embeddings

For a number field $K$ and an algebraically closed field $A$ of characteristic zero, there are exactly $n = [K : \mathbb{Q}]$ ring homomorphisms $K \to A$ (`NumberField.Embeddings.card`). The images of one element are the roots of its minimal polynomial:

**Proposition.** For $x \in K$, the set $\{\varphi(x) \mid \varphi : K \to A\}$ equals the set of roots of the minimal polynomial of $x$ over $\mathbb{Q}$ in $A$ (`NumberField.Embeddings.range_eval_eq_rootSet_minpoly`).

*Proof.* Each $\varphi(x)$ is a root, because $\varphi$ fixes the coefficients. Conversely, a root $\alpha$ gives an embedding $\mathbb{Q}(x) \to A$ with $x \mapsto \alpha$, and it extends to $K$ because $A$ is algebraically closed. $\square$

If all conjugates of an algebraic integer $x$ have absolute value at most $B$, then the coefficients of the minimal polynomial are at most $\max(B,1)^n$ times a binomial coefficient (`NumberField.Embeddings.coeff_bdd_of_norm_le`). There are finitely many integer polynomials of bounded degree and bounded coefficients, so `NumberField.Embeddings.finite_of_norm_le` follows: the set of algebraic integers of $K$ with all conjugates at most $B$ is finite.

**Theorem (Kronecker).** Let $x \ne 0$ be an algebraic integer in $K$ with $\|\varphi(x)\| \le 1$ for every embedding $\varphi$. Then $x$ is a root of unity: $x^m = 1$ for some $m > 0$ (`NumberField.Embeddings.pow_eq_one_of_norm_le_one`).

*Proof.* All powers $x^k$ are algebraic integers with conjugates of absolute value at most $1$. By the finiteness result they lie in a finite set, so $x^a = x^b$ for some $a < b$. Since $x \ne 0$, $x^{b-a} = 1$. $\square$

`NumberField.Embeddings.pow_eq_one_of_norm_eq_one` is the form with equality. This theorem is the reason why the kernel of the logarithmic embedding of Section 2 is the torsion.

The embedding $\varphi : K \to \mathbb{C}$ gives the absolute value `NumberField.place φ`, with `NumberField.place_apply` giving $|\varphi(x)|$. The conjugate embedding is `NumberField.ComplexEmbedding.conjugate φ`, the composite with complex conjugation (`NumberField.ComplexEmbedding.conjugate_coe_eq`). Conjugation is an involution (`NumberField.ComplexEmbedding.involutive_conjugate`), and the predicate `NumberField.ComplexEmbedding.IsReal φ` means $\bar\varphi = \varphi$ (`NumberField.ComplexEmbedding.isReal_iff`). A real embedding factors through $\mathbb{R}$ as `NumberField.ComplexEmbedding.IsReal.embedding`. The two conjugate embeddings give the same place (`NumberField.ComplexEmbedding.place_conjugate`).

For a field extension $L/K$ and $\sigma \in \mathrm{Gal}(L/K)$, `NumberField.ComplexEmbedding.IsConj φ σ` says that $\bar\varphi = \varphi \circ \sigma$: the automorphism $\sigma$ acts as complex conjugation through $\varphi$. If $\sigma \ne 1$ has this property, then $\sigma$ has order $2$ (`NumberField.ComplexEmbedding.orderOf_isConj_two_of_ne_one`), and $\sigma \ne 1$ exactly when $\varphi$ is not real (`NumberField.ComplexEmbedding.isConj_ne_one_iff`). For an embedding $\psi$ of the base field, `NumberField.ComplexEmbedding.LiesOver` says that $\varphi$ extends $\psi$. An embedding $\varphi$ over a real $\psi$ is mixed (`NumberField.ComplexEmbedding.IsMixed`) when $\varphi$ is not real. Then $\varphi$ and $\bar\varphi$ are two different embeddings over the same $\psi$.

#### Ramification at infinity

For a place $w$ of $L$, its restriction to $K$ is `NumberField.InfinitePlace.comap w (algebraMap K L)`, with `NumberField.InfinitePlace.comap_mk` for the place of $\varphi \circ \iota$. The place $w$ is unramified over $K$ (`NumberField.InfinitePlace.IsUnramified K w`) when it has the same multiplicity as its restriction. Here the multiplicity is $1$ for a real place and $2$ for a complex place. So the only ramified case is a complex place over a real place.

**Proposition.** $w$ is ramified over $K$ exactly when $w$ is complex and its restriction to $K$ is real (`NumberField.InfinitePlace.isRamified_iff`).

*Proof.* The multiplicity of the restriction is at most the multiplicity of $w$ (`NumberField.InfinitePlace.mult_comap_le`), because the restriction of a real embedding is real. The two multiplicities differ only when $w$ has $2$ and its restriction has $1$. $\square$

`NumberField.InfinitePlace.isUnramified_iff` is the negation: $w$ is real or its restriction is complex. In particular a real place is unramified (`NumberField.InfinitePlace.IsReal.isUnramified`). At the level of embeddings, `NumberField.InfinitePlace.isRamified_mk_iff_isMixed` says that the place of $\varphi$ is ramified exactly when $\varphi$ is mixed.

The group $\mathrm{Gal}(L/K)$ acts on the places of $L$ by $\sigma \cdot w = w \circ \sigma^{-1}$ (`NumberField.InfinitePlace.instMulActionAlgEquiv`, `NumberField.InfinitePlace.smul_mk`). The action keeps the restriction to $K$. When $L/K$ is Galois, two places with the same restriction are in one orbit (`NumberField.InfinitePlace.exists_smul_eq_of_comap_eq`), so the orbits are in bijection with the places of $K$ (`NumberField.InfinitePlace.orbitRelEquiv`).

**Proposition.** Let $L/K$ be Galois. The stabilizer of $w$ has order $1$ if $w$ is unramified and $2$ if $w$ is ramified (`NumberField.InfinitePlace.card_stabilizer`).

*Proof.* Write $w$ as the place of $\varphi$. The automorphism $\sigma$ fixes $w$ exactly when $\varphi \circ \sigma$ is $\varphi$ or $\bar\varphi$ (`NumberField.InfinitePlace.mem_stabilizer_mk_iff`). The first case gives $\sigma = 1$. The second case gives an automorphism $\sigma$ with `IsConj φ σ`; it is unique, and it is not $1$ exactly when $\varphi$ is not real. If the place is ramified, $\varphi$ is not real, and $\bar\varphi$ is again an embedding over the real restriction, so it has the form $\varphi \circ \sigma$ (`NumberField.InfinitePlace.exists_isConj_of_isRamified`). If the place is unramified, the only such $\sigma$ is $1$ (`NumberField.InfinitePlace.isUnramified_mk_iff_forall_isConj`). $\square$

A ramified place gives an element of order $2$ in the Galois group. So an extension of odd degree is unramified at every infinite place: `IsUnramifiedAtInfinitePlaces_of_odd_finrank` gives an instance of the class `IsUnramifiedAtInfinitePlaces K L`. The class is stable in towers (`IsUnramifiedAtInfinitePlaces.trans`).

Without the Galois hypothesis, the count is done place by place. For a place $v$ of $K$, `NumberField.InfinitePlace.placesOver L v` is the set of places of $L$ over $v$, and it splits as `unramifiedPlacesOver` and `ramifiedPlacesOver`.

**Proposition.** $\#\{\text{unramified } w \mid v\} + 2\,\#\{\text{ramified } w \mid v\} = [L : K]$ (`NumberField.InfinitePlace.unramifiedPlacesOver_ncard_add_eq_finrank`).

*Proof.* The embeddings of $L$ over a fixed embedding $\psi$ of $K$ with $v = |\psi|$ number $[L : K]$. If $v$ is complex, each $w$ over $v$ is unramified and has exactly one embedding over $\psi$, since the second one is over $\bar\psi$. If $v$ is real, an unramified $w$ has one real embedding over $\psi$, and a ramified $w$ has the two embeddings $\varphi$ and $\bar\varphi$ over $\psi$. $\square$

#### Totally real and totally complex fields

| Lean name | Statement |
|---|---|
| `NumberField.IsTotallyReal K` | class: every infinite place is real |
| `NumberField.IsTotallyComplex K` | class: every infinite place is complex |
| `NumberField.isTotallyReal_iff` | the class holds iff each place is real |
| `NumberField.IsTotallyReal.finrank` | $[K:\mathbb{Q}] = r_1$ |
| `NumberField.IsTotallyComplex.finrank` | $[K:\mathbb{Q}] = 2r_2$ |
| `NumberField.nrComplexPlaces_eq_zero_iff` | $r_2 = 0$ iff $K$ is totally real |
| `NumberField.IsTotallyReal.of_algebra` | a subfield of a totally real field is totally real |
| `NumberField.isTotallyComplex_of_algebra` | a field over a totally complex field is totally complex |

The maximal real subfield `NumberField.maximalRealSubfield K` is the subfield of the $x \in K$ with $\overline{\varphi(x)} = \varphi(x)$ for every embedding $\varphi$ (`NumberField.mem_maximalRealSubfield_iff`). It is totally real (`NumberField.isTotallyReal_maximalRealSubfield`), and it contains every totally real subfield (`NumberField.IsTotallyReal.le_maximalRealSubfield`). So a subfield is totally real exactly when it lies in it (`NumberField.isTotallyReal_iff_le_maximalRealSubfield`). It is all of $K$ exactly when $K$ is totally real (`NumberField.maximalRealSubfield_eq_top_iff_isTotallyReal`). The join of two totally real subfields is again totally real (`NumberField.isTotallyReal_sup`).

#### CM fields

A CM field is a totally complex field $K$ that is a quadratic extension of its maximal real subfield $K^+$. In Mathlib it is the class `NumberField.IsCMField K`, with the fields `NumberField.IsCMField.to_isTotallyComplex` and `NumberField.IsCMField.is_quadratic`. The constructors are these:

| Lean name | Statement |
|---|---|
| `NumberField.IsCMField.ofCMExtension` | $K$ totally complex and quadratic over a totally real $F$ |
| `NumberField.IsCMField.of_isAbelianGalois` | $K$ totally complex and abelian over $\mathbb{Q}$ |
| `NumberField.IsCMField.of_forall_isConj` | $K$ totally complex, Galois, and one $\sigma$ acts as complex conjugation for every embedding |
| `IsCyclotomicExtension.Rat.isCMField` | $\mathbb{Q}(\zeta_m)$ with some $m > 2$ |

In the first case, `NumberField.CMExtension.equivMaximalRealSubfield` identifies $F$ with $K^+$. The nontrivial automorphism of $K/K^+$ is `NumberField.IsCMField.complexConj K`. It acts as complex conjugation through every embedding (`NumberField.IsCMField.isConj_complexConj`), it has order $2$ (`NumberField.IsCMField.orderOf_complexConj`), and it fixes exactly $K^+$ (`NumberField.IsCMField.complexConj_eq_self_iff`). It acts on the ring of integers and on the units as `ringOfIntegersComplexConj` and `unitsComplexConj`.

Each place of $K^+$ is real and has exactly one place of $K$ over it, so `NumberField.IsCMField.equivInfinitePlace` is a bijection between the places of $K$ and those of $K^+$. With the unit theorem, the two unit groups have the same rank $r = [K^+ : \mathbb{Q}] - 1$ (`NumberField.IsCMField.units_rank_eq_units_rank`).

The image of the units of $K^+$ is the subgroup `NumberField.IsCMField.realUnits K`. The map $u \mapsto u/\bar u$ is a homomorphism `NumberField.IsCMField.unitsMulComplexConjInv` from the units to the torsion. Its kernel is the real units, since $u = \bar u$ means $u \in K^+$. It sends a root of unity $\zeta$ to $\zeta/\bar\zeta = \zeta^2$, so the image of the torsion is the group of squares (`NumberField.IsCMField.map_unitsMulComplexConjInv_torsion`).

**Theorem.** The index $Q_K = [\mathcal{O}_K^\times : \mu_K\,\mathcal{O}_{K^+}^\times]$ is $1$ or $2$ (`NumberField.IsCMField.indexRealUnits_eq_one_or_two`).

*Proof.* Let $\phi(u) = u/\bar u$. Its image lies in $\mu_K$ and contains $\mu_K^2$. The group $\mu_K$ is cyclic of even order, so $[\mu_K : \mu_K^2] = 2$. The map $\phi$ gives an isomorphism from $\mathcal{O}_K^\times/\mu_K\mathcal{O}_{K^+}^\times$ to $\phi(\mathcal{O}_K^\times)/\mu_K^2$, so $Q_K \cdot [\mu_K : \phi(\mathcal{O}_K^\times)] = 2$. This is `NumberField.IsCMField.indexRealUnits_mul_eq`. $\square$

The index $Q_K$ is `NumberField.IsCMField.indexRealUnits K`. With `NumberField.IsCMField.realFundSystem`, the images of a fundamental system of $K^+$, the regulators compare as follows (`NumberField.IsCMField.regulator_div_regulator_eq_two_pow_mul_indexRealUnits_inv`):
$$\frac{R_K}{R_{K^+}} = \frac{2^r}{Q_K}.$$
The factor $2^r$ comes from the multiplicity $2$ of every place of $K$ against $1$ for $K^+$. The factor $Q_K$ is the index of the subgroup generated by the real fundamental units and the torsion.

#### Common errors

1. A ring homomorphism `K →+* ℂ` and an infinite place are different objects. A complex place has two embeddings, and lemmas about `ComplexEmbedding` do not apply directly to `InfinitePlace`. Use `NumberField.InfinitePlace.mk` and `NumberField.InfinitePlace.embedding` to pass between them.
2. "Ramified" here is ramification at infinity, a real place under a complex place. It has no relation to the ramification of prime ideals, and an extension of odd degree is always unramified at infinity.
3. `IsCMField K` needs `IsTotallyComplex K`. The constructor `NumberField.IsCMField.of_isAbelianGalois` asks for it as an instance, so for a cyclotomic field use `IsCyclotomicExtension.Rat.isCMField`, which proves it.

### Exercises

1. (A) Use `NumberField.Embeddings.range_eval_eq_rootSet_minpoly` to list the images of $\sqrt[3]{2}$ under the three embeddings of $\mathbb{Q}(\sqrt[3]{2})$ into $\mathbb{C}$, and find the places of this field.
2. (A) Give an algebraic integer $x \ne 0$ in $\mathbb{Q}(\sqrt2)$ with $|x| \le 1$ that is not a root of unity. Explain which hypothesis of Kronecker's theorem fails.
3. (A) For $L = \mathbb{Q}(\sqrt[3]{2}, \zeta_3)$ over $K = \mathbb{Q}(\sqrt[3]{2})$, find the places of $L$ over each place of $K$ and check the formula of `NumberField.InfinitePlace.unramifiedPlacesOver_ncard_add_eq_finrank`.
4. (B) Show that $\mathbb{Q}(\sqrt{-2}, \sqrt{3})$ is a CM field and find its maximal real subfield.
5. (B) For $K = \mathbb{Q}(\zeta_5)$, show that $Q_K = 1$. Hint: every root of unity in $K$ is $\pm\eta^2$ for some $\eta \in \mu_K$. If $u/\bar u = -\eta^2$, then $v = u\eta^{-1}$ has $\bar v = -v$. Complex conjugation acts trivially on $\mathcal{O}_K/(1 - \zeta_5)$, so $2v \in (1 - \zeta_5)$, which is false for a unit.
6. (C) Let $L/K$ be Galois of odd degree. Use `NumberField.InfinitePlace.card_stabilizer` to prove that $L/K$ is unramified at every infinite place. Then give a Galois extension of even degree with one place over a real place, and show that this place is ramified.

### Reference

<?reference?>
