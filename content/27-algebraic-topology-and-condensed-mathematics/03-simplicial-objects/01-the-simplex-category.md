---
title: The simplex category
kind: theory
modules:
  - Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic
  - Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
  - Mathlib.AlgebraicTopology.SimplexCategory.Basic
  - Mathlib.AlgebraicTopology.SimplexCategory.Defs
  - Mathlib.AlgebraicTopology.SimplexCategory.DeltaZeroIter
  - Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic
  - Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.EpiMono
  - Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.NormalForms
  - Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
  - Mathlib.AlgebraicTopology.SimplexCategory.Rev
  - Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
  - Mathlib.AlgebraicTopology.SimplexCategory.ToMkOne
  - Mathlib.AlgebraicTopology.SimplexCategory.Truncated
explains:
  E3: [SimplexCategory, SimplexCategory.δ, SimplexCategory.σ, SimplexCategory.δ_comp_δ, SimplexCategory.δ_comp_σ_self, SimplexCategory.δ_comp_σ_succ, SimplexCategory.δ_comp_σ_of_le, SimplexCategory.δ_comp_σ_of_gt, SimplexCategory.σ_comp_σ, SimplexCategory.mono_iff_injective, SimplexCategory.epi_iff_surjective, SimplexCategoryGenRel, SimplexCategoryGenRel.exists_normal_form_P_σ, AugmentedSimplexCategory]
  E2: [SimplexCategory.mk, SimplexCategory.len, SimplexCategory.Hom.mk, SimplexCategory.isIso_of_bijective, SimplexCategory.iso_eq_iso_refl, SimplexCategory.instHasStrongEpiMonoFactorisations, SimplexCategory.factor_δ, SimplexCategory.skeletalEquivalence, SimplexCategory.isTerminalZero, SimplexCategory.const, SimplexCategory.mkOfLe, SimplexCategory.mkOfSucc, SimplexCategory.diag, SimplexCategory.Truncated, SimplexCategory.Truncated.inclusion, SimplexCategory.Truncated.δ₂, SimplexCategory.Truncated.σ₂, SimplexCategory.morphismProperty_eq_top, SimplexCategory.mono_induction, SimplexCategory.epi_induction, FreeSimplexQuiver, FreeSimplexQuiver.homRel, SimplexCategoryGenRel.toSimplexCategory, SimplexCategoryGenRel.P_σ, SimplexCategoryGenRel.P_δ, SimplexCategoryGenRel.exists_P_σ_P_δ_factorization, SimplexCategoryGenRel.IsAdmissible, SimplexCategoryGenRel.standardσ, AugmentedSimplexCategory.inclusion, AugmentedSimplexCategory.equivAugmentedSimplicialObject, AugmentedSimplexCategory.tensorObj, AugmentedSimplexCategory.instMonoidalCategory, AugmentedSimplexCategory.inl, AugmentedSimplexCategory.inr, SemiSimplexCategory, SemiSimplexCategory.toSimplexCategory, SimplexCategory.rev, SimplexCategory.rev_map_δ, SimplexCategory.revEquivalence, SimplexCategory.toMk₁, SimplexCategory.toMk₁_bijective, SimplexCategory.δ₀Iter, SimplexCategory.σ₀Iter]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V24.C04, V24.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The simplex category

### Overview

The simplex category $\Delta$ records how simplices meet, by finite ordered sets and order preserving maps. A functor out of $\Delta^{\mathrm{op}}$ is a simplicial object, the subject of the next two sections.

This section defines $\Delta$, its faces $\delta_i$ and degeneracies $\sigma_j$, and proves the simplicial identities. It proves the unique epi-mono factorization and the normal form of a morphism. It then reads the presented category, the augmented simplex category, the truncations and the semi-simplex category.

Mathlib writes `f ≫ g` for $g \circ f$; the text below writes $g f$.

### Definitions

For $n \geq 0$ let $[n]$ be the totally ordered set $\{0 < 1 < \dots < n\}$, with $n + 1$ elements.

**Definition (Simplex category).** The *simplex category* $\Delta$ has one object $[n]$ for each natural number $n$. A morphism $[n] \to [m]$ is a monotone map, that is a map $f$ with $f(a) \leq f(b)$ whenever $a \leq b$. Composition is composition of maps.

Each nonempty finite totally ordered set with $n + 1$ elements is uniquely isomorphic to $[n]$, so $\Delta$ is a skeleton of the category of such sets. The object $[0]$ is terminal.

::: mathlib
`SimplexCategory` · `Mathlib.AlgebraicTopology.SimplexCategory.Defs`

`SimplexCategory` is a structure with one field `len : ℕ`, and `⦋n⦌` is `SimplexCategory.mk n` after `open Simplicial`. A morphism is built by `Hom.mk` from a monotone map `Fin (n + 1) →o Fin (m + 1)`. `skeletalEquivalence` compares it with `NonemptyFinLinOrd`, and `isTerminalZero` says that `⦋0⦌` is terminal.

<?decl SimplexCategory?>
:::

**Definition (Faces and degeneracies).** For $n \geq 0$ and $0 \leq i \leq n + 1$, the *face map* $\delta_i : [n] \to [n+1]$ is the injective monotone map whose image misses $i$: $$\delta_i(k) = k \text{ if } k < i, \qquad \delta_i(k) = k + 1 \text{ if } k \geq i.$$ For $0 \leq j \leq n$, the *degeneracy map* $\sigma_j : [n+1] \to [n]$ is the surjective monotone map that sends $j$ and $j + 1$ to $j$: $$\sigma_j(k) = k \text{ if } k \leq j, \qquad \sigma_j(k) = k - 1 \text{ if } k > j.$$

The names come from geometry. The standard $(n+1)$-simplex has vertices $0, \dots, n+1$, and $\delta_i$ includes the $n$-simplex as the face opposite to the vertex $i$. The map $\sigma_j$ collapses the edge from $j$ to $j+1$ to a point.

::: mathlib
`SimplexCategory.δ` · `Mathlib.AlgebraicTopology.SimplexCategory.Basic`

`δ i : ⦋n⦌ ⟶ ⦋n + 1⦌` takes `i : Fin (n + 2)` and is `Fin.succAbove i`. `σ i : ⦋n + 1⦌ ⟶ ⦋n⦌` takes `i : Fin (n + 1)` and is `Fin.predAbove i`. Other named maps are `const`, `mkOfLe i j h`, the edge from `i` to `j`, `mkOfSucc i` and `diag n`, the edge from `0` to `n`.

<?decl SimplexCategory.δ?>
:::

**Definition (Truncation).** For $d \geq 0$ the *truncated simplex category* $\Delta_{\leq d}$ is the full subcategory of $\Delta$ on the objects $[n]$ with $n \leq d$.

**Definition (Augmented simplex category).** The *augmented simplex category* $\Delta_+$ is $\Delta$ with one more object $[-1] = \emptyset$, which is initial. Its morphisms are the monotone maps between the finite totally ordered sets $\emptyset, [0], [1], \dots$.

**Definition (Ordinal sum).** The *ordinal sum* $A \star B$ of two totally ordered sets is their disjoint union, ordered so that $A$ and $B$ keep their orders and each element of $A$ is below each element of $B$. So $[m] \star [n] \cong [m + n + 1]$, and $\emptyset \star A = A = A \star \emptyset$.

**Definition (Semi-simplex category).** The *semi-simplex category* has the same objects as $\Delta$, and its morphisms are the injective monotone maps.

### Theorems and proofs

**Theorem (Simplicial identities).** The faces and degeneracies satisfy, whenever both sides are defined:

1. $\delta_j \delta_i = \delta_i \delta_{j-1}$ for $i < j$;
2. $\sigma_j \delta_i = \delta_i \sigma_{j-1}$ for $i < j$;
3. $\sigma_j \delta_j = \mathrm{id} = \sigma_j \delta_{j+1}$;
4. $\sigma_j \delta_i = \delta_{i-1} \sigma_j$ for $i > j + 1$;
5. $\sigma_j \sigma_i = \sigma_i \sigma_{j+1}$ for $i \leq j$.

*Proof.* Each identity is an equality of maps between finite sets, so it suffices to compare the values at each point $k$. Each formula for $\delta$ and $\sigma$ has two cases, and the proof splits $k$ into ranges on which every map in the identity has one fixed case.

(1) Let $i < j$. If $k < i$, both sides give $k$. If $i \leq k < j - 1$, then $\delta_i(k) = k + 1 < j$, so the left side is $k + 1$, and the right side is $\delta_i(k) = k + 1$. If $k \geq j - 1$, the left side is $\delta_j(k+1) = k + 2$, and the right side is $\delta_i(k + 1) = k + 2$ since $k + 1 > i$.

(2) Let $i < j$. If $k < i$, both sides give $k$. If $i \leq k \leq j - 1$, both sides give $k + 1$, since $\delta_i(k) = k + 1 \leq j$ and $\sigma_{j-1}(k) = k$. If $k \geq j$, the left side is $\sigma_j(k+1) = k$ and the right side is $\delta_i(k - 1) = k$, since $k - 1 \geq i$.

(3) If $k < j$, then $\sigma_j \delta_j(k) = \sigma_j(k) = k$; if $k \geq j$, then $\sigma_j(k+1) = k$. If $k \leq j$, then $\sigma_j \delta_{j+1}(k) = \sigma_j(k) = k$; if $k > j$, then $\sigma_j(k+1) = k$.

(4) Let $i > j + 1$. If $k \leq j$, both sides give $k$. If $j < k < i$, both sides give $k - 1$, since $k - 1 < i - 1$. If $k \geq i$, both sides give $k$, since $\sigma_j(k+1) = k$ and $\delta_{i-1}(k-1) = k$.

(5) Let $i \leq j$. If $k \leq i$, both sides give $k$. If $i < k \leq j + 1$, both sides give $k - 1$. If $k > j + 1$, both sides give $k - 2$, since $\sigma_i(k) = k - 1 > j$ and $\sigma_{j+1}(k) = k - 1 > i$. $\square$

::: mathlib
`SimplexCategory.δ_comp_δ` · `Mathlib.AlgebraicTopology.SimplexCategory.Basic`

Mathlib writes $j - 1$ and $j + 1$ with `Fin.castSucc` and `Fin.succ`. For `i ≤ j`, `δ_comp_δ` is `δ i ≫ δ j.succ = δ j ≫ δ i.castSucc`, identity (1). `δ_comp_σ_of_le` is (2), `δ_comp_σ_self` and `δ_comp_σ_succ` are (3), `δ_comp_σ_of_gt` is (4) and `σ_comp_σ` is (5).

<?decl SimplexCategory.δ_comp_δ?>
:::

**Proposition (Monomorphisms and epimorphisms).** A morphism $f : [n] \to [m]$ of $\Delta$ is a monomorphism if and only if it is injective, and an epimorphism if and only if it is surjective. A morphism is an isomorphism if and only if it is the identity.

*Proof.* An injective map cancels on the left for all maps of sets, so an injective $f$ is a monomorphism. Conversely, let $f$ be a monomorphism and let $f(a) = f(b)$. The constant maps $c_a, c_b : [0] \to [n]$ at $a$ and $b$ satisfy $f c_a = f c_b$, so $c_a = c_b$ and $a = b$.

A surjective map cancels on the right, so it is an epimorphism. Conversely, let $f$ be an epimorphism and suppose that $j \in [m]$ is not in the image of $f$. Define $g, h : [m] \to [1]$ by $g(k) = 0$ for $k < j$ and $g(k) = 1$ for $k \geq j$, and $h(k) = 0$ for $k \leq j$ and $h(k) = 1$ for $k > j$. Both maps are monotone, and they differ only at $j$. Since $j$ is not a value of $f$, $g f = h f$, so $g = h$, a contradiction.

An isomorphism is bijective, so $n = m$. A monotone bijection $[n] \to [n]$ preserves the least element, then the least element of the rest, and so on; so it is the identity. $\square$

**Theorem (Epi-mono factorization).** Each morphism $f : [n] \to [m]$ is a composite $f = \iota p$ with $p : [n] \to [k]$ surjective and $\iota : [k] \to [m]$ injective. The pair $(p, \iota)$ is unique.

*Proof.* Let $S = f([n]) \subseteq [m]$ and let $k + 1$ be the number of elements of $S$. There is a unique order isomorphism $\theta : [k] \to S$. Put $\iota = \theta$ followed by the inclusion of $S$, and $p = \theta^{-1} f$. Then $\iota$ is injective and monotone, $p$ is surjective, and $p$ is monotone since $\theta^{-1}$ is. For uniqueness, let $f = \iota' p'$ be a second factorization through $[k']$. The image of $\iota'$ is the image of $f$, since $p'$ is surjective; so $k' = k$ and $\iota'$ is a monotone bijection $[k] \to S$, which is $\theta$ by uniqueness of order isomorphisms. Since $\iota$ is injective, $p' = p$. $\square$

**Theorem (Normal form).** Let $f : [n] \to [m]$ be monotone. Let $i_1 > i_2 > \dots > i_s$ be the elements of $[m]$ that are not values of $f$, and let $j_1 < j_2 < \dots < j_t$ be the elements $j$ of $[n]$ with $f(j) = f(j+1)$. Then $$f = \delta_{i_1} \delta_{i_2} \cdots \delta_{i_s} \, \sigma_{j_1} \sigma_{j_2} \cdots \sigma_{j_t},$$ and $m - s = n - t$. Conversely, an expression of this shape with $i_1 > \dots > i_s$ and $j_1 < \dots < j_t$ is the normal form of the map that it defines.

*Proof.* By the factorization theorem, $f = \iota p$, and $p$ has the same pairs $j, j+1$ with equal values as $f$, while $\iota$ has the same missing values as $f$. So it is enough to treat an injective map and a surjective map.

Let $\iota : [k] \to [m]$ be injective with missing values $i_1 > \dots > i_s$, so $s = m - k$. Induction on $s$. If $s = 0$, $\iota$ is a monotone bijection, so it is the identity. If $s > 0$, define $\iota' : [k] \to [m-1]$ by $\iota'(a) = \iota(a)$ if $\iota(a) < i_1$ and $\iota'(a) = \iota(a) - 1$ if $\iota(a) > i_1$. Then $\iota'$ is monotone and $\delta_{i_1} \iota' = \iota$. The value $q \in [m-1]$ is missing for $\iota'$ if and only if $\delta_{i_1}(q)$ is missing for $\iota$ and differs from $i_1$. As $i_2, \dots, i_s < i_1$, the map $\delta_{i_1}$ fixes them, so the missing values of $\iota'$ are $i_2 > \dots > i_s$. By induction $\iota' = \delta_{i_2} \cdots \delta_{i_s}$.

Let $p : [n] \to [k]$ be surjective with repeated positions $j_1 < \dots < j_t$, so $t = n - k$. Induction on $t$; the case $t = 0$ is as before. If $t > 0$, define $p' : [n-1] \to [k]$ by $p'(a) = p(a)$ for $a \leq j_t$ and $p'(a) = p(a + 1)$ for $a > j_t$. Then $p' \sigma_{j_t} = p$, since $p(j_t + 1) = p(j_t)$. Below $j_t$ the repeated positions of $p'$ are those of $p$, and $j_t$ is not repeated for $p'$, since $p(j_t + 2) > p(j_t + 1)$. So induction gives $p' = \sigma_{j_1} \cdots \sigma_{j_{t-1}}$.

For the converse, the same inductions show that $\delta_{i_1} \cdots \delta_{i_s}$ misses exactly $i_1, \dots, i_s$ and that $\sigma_{j_1} \cdots \sigma_{j_t}$ repeats exactly at $j_1, \dots, j_t$. By uniqueness of the factorization, these lists are the lists read off from the composite. $\square$

**Remark (Presentation).** The theorem gives a presentation of $\Delta$ by the $\delta_i$, the $\sigma_j$ and the simplicial identities. Identities (2), (3) and (4) move each degeneracy to the right of each face or cancel the pair, and (1) and (5) sort the faces and the degeneracies. So the identities alone bring each word to its normal form.

::: mathlib
`SimplexCategoryGenRel.exists_normal_form_P_σ` · `Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.NormalForms`

`FreeSimplexQuiver.homRel` lists the five identities, and `SimplexCategoryGenRel` is the quotient of the path category of `FreeSimplexQuiver` by them, with the functor `toSimplexCategory`. `P_σ` and `P_δ` are the composites of degeneracies and of faces, and `exists_P_σ_P_δ_factorization` factors each morphism through them. `standardσ` sends an `IsAdmissible` list `[i₀, …, iₙ]` to `σ iₙ ≫ ⋯ ≫ σ i₀`, and `exists_normal_form_P_σ` says that each `P_σ` map has this form. The index of this edition has no declaration for the equivalence of `SimplexCategoryGenRel` with `SimplexCategory`.

<?decl SimplexCategoryGenRel.exists_normal_form_P_σ?>
:::

**Remark (Ordinal sum).** Ordinal sum is a monoidal structure on $\Delta_+$ with unit $\emptyset$. On maps, $f \star g$ is $f$ on $A$ and $g$ on $B$; it is monotone because $f(A)$ lies below $g(B)$. The associator and unitors are identities of underlying sets, so the coherence axioms hold. A map out of $A \star B$ is determined by its restrictions to $A$ and $B$.

### Examples

**Example (Faces and degeneracies of the 2-simplex).** Write a map $[1] \to [2]$ as the pair $(f(0), f(1))$ and a map $[2] \to [1]$ as a triple. The faces are $\delta_0 = (1,2)$, $\delta_1 = (0,2)$ and $\delta_2 = (0,1)$, the three edges of the triangle. The degeneracies are $\sigma_0 = (0,0,1)$ and $\sigma_1 = (0,1,1)$. Then $\sigma_0 \delta_0 = \sigma_0 \delta_1 = (0,1)$ and $\sigma_1 \delta_1 = \sigma_1 \delta_2 = (0,1)$, as identity (3) says. Next $\sigma_0 \delta_2 = (0,0)$, which is $\delta_1 \sigma_0$ by identity (4), the constant map at $0$. Last $\sigma_1 \delta_0 = (1,1)$, which is $\delta_0 \sigma_0$ by identity (2), the constant map at $1$. For identity (1) on $[0] \to [2]$: $\delta_2 \delta_0 = \delta_0 \delta_1$ is the vertex $1$, $\delta_2 \delta_1 = \delta_1 \delta_1$ is the vertex $0$ and $\delta_1 \delta_0 = \delta_0 \delta_0$ is the vertex $2$.

**Example (A normal form).** Let $f : [3] \to [2]$ be $(0, 0, 2, 2)$. The missing value is $1$, so $s = 1$ and $i_1 = 1$. The repeated positions are $0$ and $2$, so $t = 2$. The theorem gives $f = \delta_1 \sigma_0 \sigma_2$, and $m - s = 1 = n - t$. Check: $\sigma_2 : [3] \to [2]$ is $(0, 1, 2, 2)$, then $\sigma_0 : [2] \to [1]$ gives $(0, 0, 1, 1)$, then $\delta_1 : [1] \to [2]$ is $(0, 2)$ and gives $(0, 0, 2, 2)$.

```lean
open SimplexCategory Simplicial in
example : δ (Fin.castSucc (0 : Fin 2)) ≫ σ 0 = 𝟙 ⦋1⦌ :=
  δ_comp_σ_self
```

**Counterexample (Monomorphisms of the semi-simplex category).** In the semi-simplex category each morphism is injective, so the degeneracies are absent and the normal form has only faces. The map $\sigma_0 : [1] \to [0]$ has no analogue there. The functor to $\Delta$ is faithful but not full.

### The library around it

::: mathlib
`SimplexCategory.epi_iff_surjective` · `Mathlib.AlgebraicTopology.SimplexCategory.Basic`

`mono_iff_injective` and `epi_iff_surjective` are the proposition on monomorphisms and epimorphisms, and `isIso_of_bijective` and `iso_eq_iso_refl` treat isomorphisms. `factor_δ` factors a map that misses a value through a face. The instance `instHasStrongEpiMonoFactorisations` is the factorization theorem.

<?decl SimplexCategory.epi_iff_surjective?>
:::

`SimplexCategory.morphismProperty_eq_top` says that a multiplicative class of morphisms that contains all `δ i` and `σ i` is `⊤`; `mono_induction` and `epi_induction` are the versions for faces and degeneracies.

`SimplexCategory.Truncated d` is the full subcategory on `⦋n⦌` with `n ≤ d`, with `Truncated.inclusion d`. `Truncated.δ₂` and `Truncated.σ₂` are the faces and degeneracies of the 2-truncation, which Chapter 4 uses.

::: mathlib
`AugmentedSimplexCategory` · `Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic`

`AugmentedSimplexCategory` is `WithInitial SimplexCategory`, with the initial object `star` in the part of $[-1] = \emptyset$. `equivAugmentedSimplicialObject` identifies functors out of its opposite with the augmented simplicial objects of Section 2. `tensorObj` is the ordinal sum, with `⦋m⦌ ⊗ ⦋n⦌ = ⦋m + n + 1⦌`, `instMonoidalCategory` is the monoidal structure and `inl`, `inr` are the two inclusions.

<?decl AugmentedSimplexCategory?>
:::

`SemiSimplexCategory.toSimplexCategory` is the faithful functor from the semi-simplex category. `SimplexCategory.rev` sends $f$ to $i \mapsto m - f(n - i)$; `rev_map_δ` sends `δ i` to `δ i.rev` and `revEquivalence` is the self-equivalence. `toMk₁ i : ⦋n⦌ ⟶ ⦋1⦌` is $0$ below $i$ and $1$ from $i$ on, and `toMk₁_bijective` says that these $n + 2$ maps are all the maps to $[1]$. `δ₀Iter` and `σ₀Iter` iterate $\delta_0$ and $\sigma_0$.

Common errors of a learner:

- `δ i ≫ δ j` means $\delta_j \delta_i$: the map written first acts first. An identity copied from a book with the factors in book order is false in Lean.
- The index of `δ i : ⦋n⦌ ⟶ ⦋n + 1⦌` has type `Fin (n + 2)`, and that of `σ i : ⦋n + 1⦌ ⟶ ⦋n⦌` has type `Fin (n + 1)`. In identities the shifts $j - 1$ and $j + 1$ appear as `Fin.castSucc` and `Fin.succ`, not as subtraction.
- `⦋n⦌` has $n + 1$ elements. The object with no element exists only in `AugmentedSimplexCategory`.
- `SimplexCategoryGenRel` is a separate category. Mathlib does not yet identify it with `SimplexCategory`.

### Exercises

1. (A) List all monotone maps $[2] \to [2]$ and write each in normal form. *Hint:* there are $10$ of them.
2. (A) Show that the number of morphisms $[n] \to [m]$ in $\Delta$ is $\binom{n + m + 1}{n + 1}$. *Hint:* a monotone map is a multiset of size $n + 1$ in a set of size $m + 1$.
3. (A) Check identity (5) on $[2] \to [0]$: show that $\sigma_0 \sigma_0 = \sigma_0 \sigma_1$ by computing both sides.
4. (B) Show that every monomorphism of $\Delta$ is split and every epimorphism of $\Delta$ is split. *Hint:* for a surjection $p$, send each value to the least point of its fibre.
5. (B) Show that $\Delta$ has no coproduct of $[0]$ and $[0]$. *Hint:* count maps into $[1]$ and then into $[2]$.
6. (C) Prove that the reversal $r$ with $r(f)(i) = m - f(n - i)$ for $f : [n] \to [m]$ is a functor, that $r(\delta_i) = \delta_{n+1-i}$ and $r(\sigma_j) = \sigma_{n-j}$, and that $r$ is not isomorphic to the identity functor. *Hint:* a natural isomorphism would be the identity on each object by the proposition on isomorphisms.

### Notes and history

Eilenberg and Zilber introduced semi-simplicial complexes with faces and degeneracies in 1950. Gabriel and Zisman (1967) use the normal form and the presentation throughout, and Mathlib cites Kerodon for the normal forms. Mac Lane shows that $\Delta_+$ with ordinal sum is the free monoidal category on a monoid; the index of this edition has no declaration for this universal property.

The Mathlib Authors of `SimplexCategory.Defs` are Johan Commelin, Kim Morrison and Adam Topaz, and of `SimplexCategory.Basic` Johan Commelin, Kim Morrison, Adam Topaz and Joël Riou. `Truncated` is by Jakob von Raumer. `Augmented.Basic`, `Augmented.Monoidal` and the three files `GeneratorsRelations.Basic`, `GeneratorsRelations.EpiMono` and `GeneratorsRelations.NormalForms` are by Robin Carlier. `DeltaZeroIter`, `MorphismProperty`, `Rev`, `SemiSimplexCategory` and `ToMkOne` are by Joël Riou.

### Reference

<?reference?>
