---
title: Nakayama's lemma and minimal generators
kind: theory
modules:
  - Mathlib.RingTheory.Finiteness.Nakayama
  - Mathlib.RingTheory.LocalRing.Module
explains:
  E3: [Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul, IsLocalRing.map_mkQ_eq_top]
  E2: [Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul, IsLocalRing.map_mkQ_eq, IsLocalRing.span_eq_top_of_tmul_eq_basis, IsLocalRing.subsingleton_tensorProduct]
  E1: auto
families: []
requires: [V07, V10.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Nakayama's lemma and minimal generators

### Overview

Nakayama's lemma says that a finitely generated module $M$ over a local ring $(R, \mathfrak m)$ with $\mathfrak m M = M$ is zero. In other words, the vector space $M/\mathfrak m M$ over the residue field sees whether $M$ is zero, and more generally which sets generate $M$. Linear algebra over the field $k = R/\mathfrak m$ then controls the generators of $M$: every basis of $M/\mathfrak m M$ lifts to a minimal set of generators of $M$, and all minimal sets of generators have $\dim_k M/\mathfrak m M$ elements.

The proof is the determinant trick of Chapter 1, Section 1. The section proves the general form for any ring and any ideal, then the form for the Jacobson radical, then the consequences over a local ring.

The section uses the local rings and residue fields of Section 1.

### Definitions

**Definition ($IM$).** Let $I$ be an ideal of $R$ and $M$ an $R$-module. The submodule $IM$ is the set of finite sums $\sum a_i x_i$ with $a_i \in I$ and $x_i \in M$. For a submodule $N \subseteq M$, $IN$ is defined in the same way. The quotient $M/IM$ is a module over $R/I$.

For a local ring $(R, \mathfrak m, k)$, $M/\mathfrak m M$ is a vector space over $k$. It is isomorphic to $k \otimes_R M$, the base change of $M$ to the residue field.

**Definition (Minimal set of generators).** A finite set of generators of $M$ is minimal if no proper subset generates $M$. The number $\mu(M)$ is the least number of elements of a set of generators of $M$.

Over a field, a set of generators is minimal if and only if it is a basis, and all bases have the same size. Over a general ring both statements fail: the sets $\{2, 3\}$ and $\{1\}$ are minimal sets of generators of $\mathbb{Z}$. Over a local ring Nakayama's lemma makes both statements true again.

::: mathlib
`Submodule.spanRank` · `Mathlib.Algebra.Module.SpanRank`

`N.spanRank` is the least cardinal of a set that spans the submodule `N`, a value in `Cardinal`. It is the number $\mu(N)$ of this section, for any module, finitely generated or not.

<?decl Submodule.spanRank?>
:::

### Theorems and proofs

**Theorem (Nakayama, determinant form).** Let $R$ be a commutative ring, $I$ an ideal and $M$ a finitely generated $R$-module with $IM = M$. Then there is $r \in R$ with $r \equiv 1 \pmod I$ and $rM = 0$.

*Proof.* Let $x_1, \ldots, x_n$ generate $M$. Each $x_i$ lies in $IM$, so $x_i = \sum_j a_{ij} x_j$ with $a_{ij} \in I$. Let $A = (a_{ij})$ and $B = 1_n - A$, a matrix over $R$. Then $B x = 0$, where $x$ is the column vector of the $x_i$. Multiply on the left by the adjugate matrix of $B$: since $\operatorname{adj}(B) B = \det(B) \cdot 1_n$, this gives $\det(B) x_i = 0$ for all $i$. So $r = \det(B)$ kills $M$. Expand the determinant: every term other than the product of the diagonal entries $1$ contains a factor from $I$, so $\det(1_n - A) \equiv 1 \pmod I$. $\square$

The same argument proves the theorem for a finitely generated submodule $N$ with $N \subseteq IN$: the relations $x_i = \sum a_{ij} x_j$ hold inside $N$.

::: mathlib
`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` · `Mathlib.RingTheory.Finiteness.Nakayama`

The theorem for a finitely generated submodule `N` with `N ≤ I • N`: there is `r` with `r - 1 ∈ I` and `r • n = 0` for all `n ∈ N`. The variant `Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul` gives `r ∈ I` with `r • n = n`, the element $1 - r$ in the notation above. To use it for a whole module, take `N = ⊤`; then `I • ⊤` is $IM$.

<?decl Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul?>
:::

**Corollary (Nakayama, Jacobson form).** Let $I$ be an ideal contained in the Jacobson radical of $R$, and $M$ a finitely generated module with $IM = M$. Then $M = 0$.

*Proof.* Take $r$ as in the theorem, $r = 1 + a$ with $a \in I$. For every maximal ideal $\mathfrak n$, $a \in \mathfrak n$, so $r \notin \mathfrak n$. An element outside all maximal ideals is a unit. So $r$ is a unit, and $rM = 0$ gives $M = 0$. $\square$

The finiteness is necessary. The $\mathbb{Z}_{(p)}$-module $\mathbb{Q}$ satisfies $p\mathbb{Q} = \mathbb{Q}$, but it is not zero.

**Corollary (Nakayama, submodule form).** Let $I$ lie in the Jacobson radical, $M$ a module, $N \subseteq M$ a submodule, and assume $M$ is finitely generated. If $M = N + IM$, then $M = N$.

*Proof.* Apply the Jacobson form to $M/N$: it is finitely generated, and $I(M/N) = (IM + N)/N = M/N$. So $M/N = 0$. $\square$

::: mathlib
`Submodule.le_of_le_smul_of_le_jacobson` · `Mathlib.RingTheory.Nakayama`

The submodule form, in a module of Volume 9, Commutative algebra I: if `N'` is finitely generated, `I ≤ Ring.jacobson R` and `N' ≤ N ⊔ I • N'`, then `N' ≤ N`. The file `Mathlib/RingTheory/Nakayama.lean` has the other forms with the Jacobson radical.

<?decl Submodule.le_of_le_smul_of_le_jacobson?>
:::

Now let $(R, \mathfrak m, k)$ be local, so that the Jacobson radical is $\mathfrak m$ (Section 1).

**Theorem (Generators over a local ring).** Let $M$ be a finitely generated module over a local ring $(R, \mathfrak m, k)$ and $x_1, \ldots, x_n \in M$. Then $x_1, \ldots, x_n$ generate $M$ if and only if their images $\bar x_1, \ldots, \bar x_n$ span the $k$-vector space $M/\mathfrak m M$.

*Proof.* If the $x_i$ generate $M$, their images generate $M/\mathfrak m M$. Conversely, let $N = Rx_1 + \cdots + Rx_n$. If the images span $M/\mathfrak m M$, then $N + \mathfrak m M = M$. The submodule form with $I = \mathfrak m$ gives $N = M$. $\square$

::: mathlib
`IsLocalRing.map_mkQ_eq_top` · `Mathlib.RingTheory.LocalRing.Module`

For a finite module `M` over a local ring and a submodule `N`: the image of `N` in `M ⧸ (maximalIdeal R • ⊤)` is everything if and only if `N = ⊤`. The theorem above is this lemma with `N` the span of the $x_i$. The relative form `IsLocalRing.map_mkQ_eq` compares two submodules `N₁ ≤ N₂` with `N₂` finitely generated.

<?decl IsLocalRing.map_mkQ_eq_top?>
:::

**Corollary (Minimal generators).** Let $M$ be a finitely generated module over a local ring $(R, \mathfrak m, k)$ and $d = \dim_k M/\mathfrak m M$.

1. A set of generators of $M$ is minimal if and only if its image is a basis of $M/\mathfrak m M$.
2. Every basis of $M/\mathfrak m M$ lifts to a minimal set of generators of $M$.
3. Every minimal set of generators of $M$ has $d$ elements, and $\mu(M) = d$.

*Proof.* The space $M/\mathfrak m M$ is finite dimensional, since the images of generators of $M$ span it. (2) Lift a basis $\bar x_1, \ldots, \bar x_d$ to $x_1, \ldots, x_d \in M$. By the theorem they generate $M$. A proper subset has an image that does not span $M/\mathfrak m M$, so by the theorem it does not generate $M$. (1) Let $x_1, \ldots, x_n$ generate $M$. The images span $M/\mathfrak m M$. If they are not a basis, some $\bar x_i$ is a linear combination of the others, so the others span, and by the theorem the $x_j$ with $j \ne i$ generate $M$. So the set is not minimal. If the images are a basis, (2) shows that the set is minimal. (3) By (1), every minimal set of generators has $d$ elements, since all bases of $M/\mathfrak m M$ have $d$ elements. A set of generators has an image that spans $M/\mathfrak m M$, so it has at least $d$ elements, and by (2) a set of $d$ generators exists. So $\mu(M) = d$. $\square$

The point of (3): over a local ring, every set of generators of $M$ can be shrunk to a minimal one, and all minimal ones have the same size. Over $\mathbb{Z}$ this fails, as the sets $\{2, 3\}$ and $\{1\}$ show.

**Corollary (Embedding dimension).** Let $(R, \mathfrak m, k)$ be a Noetherian local ring. The least number of generators of the ideal $\mathfrak m$ is $\dim_k \mathfrak m/\mathfrak m^2$.

*Proof.* Apply the previous corollary to $M = \mathfrak m$, which is finitely generated since $R$ is Noetherian. Then $\mathfrak m M = \mathfrak m^2$. $\square$

The space $\mathfrak m/\mathfrak m^2$ is the cotangent space of $R$, and its dimension is the embedding dimension of $R$. For the local ring of a variety at a point, it is the dimension of the Zariski tangent space. Chapter 7 compares it with the Krull dimension: the two are equal exactly for regular local rings.

::: mathlib
`IsLocalRing.rank_cotangentSpace_eq_spanrank_maximalIdeal` · `Mathlib.RingTheory.Ideal.Cotangent`

For a Noetherian local ring: `Module.rank (ResidueField R) (CotangentSpace R) = (maximalIdeal R).spanRank`. The type `IsLocalRing.CotangentSpace R` is $\mathfrak m/\mathfrak m^2$ as a vector space over the residue field. Both are in a module of Volume 9, Commutative algebra I.

<?decl IsLocalRing.rank_cotangentSpace_eq_spanrank_maximalIdeal?>
:::

### Examples

**Example (Generators of an ideal of $\mathbb{Z}_{(p)}$).** In $R = \mathbb{Z}_{(p)}$ with $\mathfrak m = (p)$, the ideal $\mathfrak m$ has $\mathfrak m/\mathfrak m^2 \cong \mathbb{F}_p$, of dimension $1$. So one element generates $\mathfrak m$, and an element $x \in \mathfrak m$ generates it exactly when $x \notin \mathfrak m^2$. For example $x = 6p$ works when $p \ne 2, 3$, since $6$ is a unit, and $x = p^2$ does not.

**Example (Two variables).** Let $R = k[X, Y]_{(X, Y)}$, the localization of the polynomial ring at the origin, with $\mathfrak m = (X, Y)$. Then $\mathfrak m/\mathfrak m^2$ has the basis $\bar X, \bar Y$, so $\mathfrak m$ needs two generators. The elements $X + Y^2$ and $Y + X^3$ also generate $\mathfrak m$, since their images are $\bar X$ and $\bar Y$. The elements $X$ and $X + Y^2$ do not, since both images lie on the line spanned by $\bar X$.

**Example (A singular point).** Let $R = k[X, Y]_{(X, Y)}/(Y^2 - X^3)$, the local ring of the cusp at the origin. Its maximal ideal $\mathfrak m = (x, y)$ satisfies $\mathfrak m^2 = (x^2, xy, y^2)$, and $y^2 = x^3 \in \mathfrak m^2$ adds nothing new in degree $1$. So $\dim_k \mathfrak m/\mathfrak m^2 = 2$. The ring has Krull dimension $1$ (Chapter 7) but needs two generators for $\mathfrak m$. This is the algebraic form of the statement that the cusp is singular.

**Example (Without finiteness).** Let $R = \mathbb{Z}_{(p)}$ and $M = \mathbb{Q}$. Then $\mathfrak m M = p\mathbb{Q} = \mathbb{Q}$, so $M/\mathfrak m M = 0$, but $M \ne 0$. The empty set spans $M/\mathfrak m M$ and does not generate $M$. The theorem needs $M$ finitely generated.

### The library around it

The determinant form is in `Mathlib/RingTheory/Finiteness/Nakayama.lean`, and the forms with the Jacobson radical are in `Mathlib/RingTheory/Nakayama.lean`, in Volume 9. The file `Mathlib/RingTheory/LocalRing/Module.lean` states the consequences over a local ring, often with the tensor product `ResidueField R ⊗[R] M` in place of the quotient $M/\mathfrak m M$. For example, `IsLocalRing.subsingleton_tensorProduct` says that a finite module `M` is zero if and only if `ResidueField R ⊗[R] M` is zero, and `IsLocalRing.span_eq_top_of_tmul_eq_basis` says that elements whose images form a basis of `ResidueField R ⊗[R] M` span `M`. The same file proves that a finite flat module over a local ring is free, a result of Chapter 8.

Common errors of a learner:

- In Lean the module $IM$ is `I • (⊤ : Submodule R M)`, and the quotient $M/\mathfrak m M$ is `M ⧸ (maximalIdeal R • ⊤ : Submodule R M)`. The tensor product form is often easier, since it has a module structure over the residue field by instance.
- The determinant form needs only `N.FG`, not a Noetherian ring.
- The Jacobson form needs `I ≤ Ring.jacobson R`. Over a local ring use `IsLocalRing.maximalIdeal_le_jacobson` or the equality with the Jacobson radical from Section 1.

### Exercises

1. (A) Let $M$ be a finitely generated module over a local ring with $M/\mathfrak m M = 0$. Show directly from the theorem on generators that $M = 0$.
2. (A) Find the least number of generators of the ideal $(X^2, XY, Y^2)$ of $k[X, Y]_{(X, Y)}$.
3. (A) Show that $\mathbb{Q}$ is not finitely generated as a $\mathbb{Z}_{(p)}$-module.
4. (B) Let $(R, \mathfrak m)$ be local and $f : M \to N$ a map of finitely generated modules such that $M/\mathfrak m M \to N/\mathfrak m N$ is surjective. Show that $f$ is surjective.
5. (B) Let $M$ be a finitely generated $R$-module and $f : M \to M$ a surjective endomorphism. View $M$ as an $R[t]$-module with $t$ acting by $f$, and apply the determinant form with $I = (t)$ to show that $f$ is injective.
6. (B) Let $I$ be a finitely generated ideal with $I = I^2$. Show that $I = (e)$ for an idempotent $e$.
7. (B) Let $(R, \mathfrak m)$ be a Noetherian local ring with $\mathfrak m = \mathfrak m^2$. Show that $R$ is a field.
8. (C) Let $(R, \mathfrak m, k)$ be local and $M$ a finitely generated projective $R$-module. Lift a basis of $M/\mathfrak m M$ to $x_1, \ldots, x_d$, consider the surjection $R^d \to M$, and show that its kernel $K$ satisfies $K = \mathfrak m K$. Conclude that $M$ is free.

### Notes and history

The lemma is named after Tadasi Nakayama. Nakayama himself attributed it to Krull and to Azumaya, and the lemma is also called the Krull-Azumaya lemma. The determinant trick is the proof of Atiyah and Macdonald, Proposition 2.4 and Corollary 2.5. Exercise 5 is a theorem of Vasconcelos (1969).

### Reference

<?reference?>
