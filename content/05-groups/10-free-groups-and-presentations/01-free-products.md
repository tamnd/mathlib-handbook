---
title: Free products of monoids and groups
kind: api
modules:
  - Mathlib.GroupTheory.Coprod.Basic
  - Mathlib.GroupTheory.CoprodI
explains:
  E2: [Monoid.Coprod.lift, Monoid.Coprod.hom_ext, Monoid.Coprod.inl_injective, Monoid.Coprod.toProd_surjective, Monoid.CoprodI.lift, Monoid.CoprodI.Word.equiv, Monoid.CoprodI.lift_injective_of_ping_pong]
  E1: auto
families: []
requires: [V05.C01, V05.C02, V05.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Free products of monoids and groups

### Overview

The product $M \times N$ of Chapter 2 is the product in the category of monoids: a pair of homomorphisms into $M$ and $N$ is the same as one homomorphism into $M \times N$. The free product $M * N$ is the dual object. A pair of homomorphisms out of $M$ and $N$ into a monoid $P$ is the same as one homomorphism $M * N \to P$. Its elements are words $m_1 n_1 m_2 n_2 \cdots$ with letters from the two factors, and no relation between letters of different factors holds in it. For groups, the free product of two copies of $\mathbb{Z}$ is the free group on two generators, and $\mathbb{Z}/2 * \mathbb{Z}/2$ is the infinite dihedral group.

The library has two forms. The module `Mathlib.GroupTheory.Coprod.Basic` defines the free product `Monoid.Coprod M N` of two monoids, with the notation `M ∗ N`. The module `Mathlib.GroupTheory.CoprodI` defines the free product `Monoid.CoprodI M` of a family $(M_i)_{i \in \iota}$. It also proves that each element has a unique reduced word, and it proves the ping-pong lemma, the standard test that a family of subgroups generates their free product. The ping-pong lemma uses the group actions of Chapter 6.

### The library around it

#### The free product of two monoids

Let $M$ and $N$ be monoids. The type `Monoid.Coprod M N` is the quotient of the free monoid `FreeMonoid (M ⊕ N)` by the congruence `Monoid.coprodCon M N`. This is the smallest congruence that identifies the letter $1_M$ and the letter $1_N$ with the empty word, and the word of two letters $x, y$ from the same factor with the one letter $xy$. The additive form is `AddMonoid.Coprod M N`, with no notation. The same type serves for monoids and for groups: when $M$ and $N$ are groups, the instance `Monoid.Coprod.instGroup` gives a group structure on `M ∗ N`. The inverse reverses a word and inverts each letter, as `Monoid.Coprod.inv_def` states.

The library gives these maps.

| Lean name | Statement |
|---|---|
| `Monoid.Coprod.mk` | the quotient map `FreeMonoid (M ⊕ N) →* M ∗ N` |
| `Monoid.Coprod.inl` | the inclusion `M →* M ∗ N` |
| `Monoid.Coprod.inr` | the inclusion `N →* M ∗ N` |
| `Monoid.Coprod.lift` | from $f : M \to P$ and $g : N \to P$, the homomorphism $M * N \to P$ |
| `Monoid.Coprod.map` | from $f : M \to M'$ and $g : N \to N'$, the homomorphism $M * N \to M' * N'$ |
| `Monoid.Coprod.swap` | the homomorphism $M * N \to N * M$ that exchanges the factors |
| `Monoid.Coprod.fst` | the projection $M * N \to M$ that kills $N$ |
| `Monoid.Coprod.snd` | the projection $M * N \to N$ that kills $M$ |
| `Monoid.Coprod.toProd` | the homomorphism $M * N \to M \times N$ |

The simp lemmas compute each map on the two inclusions. Their names follow one pattern: `Monoid.Coprod.lift_apply_inl` says $\mathrm{lift}\,f\,g\,(\mathrm{inl}\,x) = f(x)$, and the lemmas `Monoid.Coprod.fst_apply_inr`, `Monoid.Coprod.swap_inl`, `Monoid.Coprod.map_apply_inr` and `Monoid.Coprod.toProd_apply_inl` do the same for the other maps. The forms with composition, such as `Monoid.Coprod.lift_comp_inl`, state the same facts as equalities of homomorphisms.

**The universal property.** Let $P$ be a monoid, and let $f : M \to P$ and $g : N \to P$ be homomorphisms. Then `Monoid.Coprod.lift f g` is the unique homomorphism $h : M * N \to P$ with $h \circ \mathrm{inl} = f$ and $h \circ \mathrm{inr} = g$.

*Proof.* The function `Sum.elim f g` on letters extends to a homomorphism on the free monoid. This homomorphism sends $1_M$ and $1_N$ to $1$, and it sends a word $xy$ of two letters from one factor to $f(x)f(y) = f(xy)$. So it is constant on the classes of the congruence and it goes down to the quotient. For uniqueness, the images of $\mathrm{inl}$ and $\mathrm{inr}$ generate $M * N$ as a monoid (`Monoid.Coprod.mrange_inl_sup_mrange_inr`), and two homomorphisms that agree on a generating set are equal. $\square$

The lemma `Monoid.Coprod.hom_ext` is this uniqueness: two homomorphisms out of `M ∗ N` are equal when they agree after composition with `Monoid.Coprod.inl` and with `Monoid.Coprod.inr`. It is an extensionality lemma, so the tactic *ext* reduces a goal `f = g` to two goals, one for each factor. The lemma `Monoid.Coprod.lift_unique` is the same fact with `Monoid.Coprod.lift` on one side. The equivalence `Monoid.Coprod.liftEquiv` packs the universal property as a bijection between pairs of homomorphisms and homomorphisms out of the free product. The definition `Monoid.Coprod.clift` builds a homomorphism out of `M ∗ N` from a homomorphism out of the free monoid, and lets the user choose the function that Lean computes with.

**The inclusions are injective.** The composite $\mathrm{fst} \circ \mathrm{inl}$ is the identity of $M$, by `Monoid.Coprod.fst_comp_inl`. A map with a left inverse is injective, so `Monoid.Coprod.inl_injective` holds, and `Monoid.Coprod.inr_injective` follows from `Monoid.Coprod.snd` in the same way. So $M$ and $N$ are submonoids of $M * N$. The map $\mathrm{toProd}$ is surjective (`Monoid.Coprod.toProd_surjective`), because $(m, n)$ is the image of $\mathrm{inl}(m)\,\mathrm{inr}(n)$. Its kernel is large: for groups $G$ and $H$, the element $\mathrm{inl}(g)\,\mathrm{inr}(h)\,\mathrm{inl}(g)^{-1}\,\mathrm{inr}(h)^{-1}$ maps to $1$, and it is not $1$ when $g \ne 1$ and $h \ne 1$.

For the image of a homomorphism out of the free product, `Monoid.Coprod.mrange_lift` says that the range of $\mathrm{lift}\,f\,g$ is the submonoid generated by the ranges of $f$ and $g$. For groups, `Monoid.Coprod.range_lift` says the same for subgroups, and `Monoid.Coprod.closure_range_inl_union_inr` says that the two factors generate `G ∗ H` as a group.

**Induction.** To prove a statement for each element of `M ∗ N`, use `Monoid.Coprod.induction_on`. It asks for the statement on $\mathrm{inl}(m)$, on $\mathrm{inr}(n)$, and its stability under products.

**Isomorphisms.** The free product has the expected algebra up to isomorphism, with equivalences in the namespace `MulEquiv`.

| Lean name | Statement |
|---|---|
| `MulEquiv.coprodCongr` | $M \cong N$ and $M' \cong N'$ give $M * M' \cong N * N'$ |
| `MulEquiv.coprodComm` | $M * N \cong N * M$ |
| `MulEquiv.coprodAssoc` | $(M * N) * P \cong M * (N * P)$ |
| `MulEquiv.coprodPUnit` | $M * 1 \cong M$ |
| `MulEquiv.punitCoprod` | $1 * M \cong M$ |

Each of them comes from `Monoid.Coprod.lift` and `Monoid.Coprod.map`, and the inverse identities follow from `Monoid.Coprod.hom_ext`. The lemma `Monoid.Coprod.swap_swap` is the identity behind `MulEquiv.coprodComm`.

#### The free product of a family

Let $(M_i)_{i \in \iota}$ be a family of monoids. The type `Monoid.CoprodI M` is the quotient of the free monoid on the letters $\langle i, x \rangle$ with $x \in M_i$ by the congruence that `Monoid.CoprodI.Rel` generates. The relation identifies $\langle i, 1 \rangle$ with the empty word, and $\langle i, x \rangle \langle i, y \rangle$ with $\langle i, xy \rangle$. The inclusion of the factor $M_i$ is `Monoid.CoprodI.of`. When each $M_i$ is a group, `Monoid.CoprodI.instGroup` makes `Monoid.CoprodI M` a group.

The universal property is the equivalence `Monoid.CoprodI.lift`: a family of homomorphisms $f_i : M_i \to N$ is the same as one homomorphism out of the free product. The lemma `Monoid.CoprodI.lift_of` computes it: $\mathrm{lift}\,f\,(\mathrm{of}\,m) = f_i(m)$ for $m \in M_i$. The extensionality lemma `Monoid.CoprodI.ext_hom` checks the equality of two homomorphisms on each factor. Each inclusion is injective (`Monoid.CoprodI.of_injective`), because the lift of the family that is the identity on $M_i$ and trivial on the other factors is a left inverse (`Monoid.CoprodI.of_leftInverse`). The range of a lift is the supremum of the ranges, by `Monoid.CoprodI.mrange_eq_iSup` for monoids and `Monoid.CoprodI.range_eq_iSup` for groups. The two induction principles `Monoid.CoprodI.induction_on` and `Monoid.CoprodI.induction_left` reduce a statement to the generators.

#### Reduced words

The quotient form makes the universal property easy, but it does not tell when two elements are distinct. Reduced words answer this question. A reduced word is a list of letters $\langle i_1, x_1 \rangle \cdots \langle i_n, x_n \rangle$ with each $x_k \ne 1$ and $i_k \ne i_{k+1}$ for each $k$. The structure `Monoid.CoprodI.Word M` holds such a list with these two conditions. The empty word is `Monoid.CoprodI.Word.empty`, and `Monoid.CoprodI.Word.prod` sends a word to the product of its letters in the free product.

**Normal form.** Assume that $\iota$ and each $M_i$ have decidable equality. Then `Monoid.CoprodI.Word.prod` is a bijection, with inverse `Monoid.CoprodI.Word.equiv`. So each element of the free product is the product of exactly one reduced word.

*Proof sketch.* Surjectivity is easy: delete the letters $1$, and multiply adjacent letters from the same factor, until the word is reduced. Injectivity is the difficult part, and the proof uses an action. Each factor $M_i$ acts on reduced words: $m \in M_i$ multiplies the first letter when it comes from $M_i$, puts $m$ in front otherwise, and deletes the first letter when the product is $1$. The equivalence `Monoid.CoprodI.Word.equivPair` splits a word into its head in $M_i$ and the tail, and the instance `Monoid.CoprodI.Word.summandAction` is the action that it gives. By the universal property, the actions of the factors combine to an action of the free product. The lemma `Monoid.CoprodI.Word.prod_smul` says $\mathrm{prod}(m \cdot w) = m \cdot \mathrm{prod}(w)$. Apply it to $w = \mathrm{empty}$: the element $m$ is the product of the word $m \cdot \mathrm{empty}$. So $m \mapsto m \cdot \mathrm{empty}$ is a right inverse of $\mathrm{prod}$. Induction on words, with `Monoid.CoprodI.Word.smul_induction`, shows that $\mathrm{prod}(w) \cdot \mathrm{empty} = w$, so it is also a left inverse. $\square$

A consequence: the instance `Monoid.CoprodI.Word.instDecidableEq` gives decidable equality of words, and the normal form transfers it to the free product. The constructors `Monoid.CoprodI.Word.cons` and `Monoid.CoprodI.Word.rcons` put a letter in front of a word, and `Monoid.CoprodI.Word.prod_cons` computes the product. The recursor `Monoid.CoprodI.Word.consRecOn` and the principle `Monoid.CoprodI.Word.smul_induction` give induction on words.

For the ping-pong lemma the library needs words with a known first and last factor. The inductive type `Monoid.CoprodI.NeWord M i j` holds the nonempty reduced words that start with a letter from $M_i$ and end with a letter from $M_j$. Its constructors are `Monoid.CoprodI.NeWord.singleton` and `Monoid.CoprodI.NeWord.append`, the second of which asks that the last factor of the first word differs from the first factor of the second word. The functions `Monoid.CoprodI.NeWord.head`, `Monoid.CoprodI.NeWord.last`, `Monoid.CoprodI.NeWord.prod`, `Monoid.CoprodI.NeWord.toWord` and, for groups, `Monoid.CoprodI.NeWord.inv` complete the API.

#### The ping-pong lemma

Let $G$ be a group that acts on a set $\alpha$, and let $f_i : H_i \to G$ be homomorphisms from groups. Assume that there are nonempty pairwise disjoint subsets $X_i \subseteq \alpha$ such that $f_i(h) \cdot X_j \subseteq X_i$ for each $i \ne j$ and each $h \ne 1$ in $H_i$. Assume also that $\iota$ has at least three elements, or that some $H_i$ has at least three elements. Then the lift $\coprod_i H_i \to G$ is injective. This is `Monoid.CoprodI.lift_injective_of_ping_pong`. So the images of the $H_i$ generate a subgroup of $G$ that is isomorphic to their free product.

*Proof sketch.* Take a nonempty reduced word $w = h_1 h_2 \cdots h_n$ with $h_1 \in H_i$ and $h_n \in H_j$. Choose an index $k \ne j$. The last letter moves $X_k$ into $X_j$, the letter before moves it into its own set, and so on, so the image of $w$ moves $X_k$ into $X_i$. This is `Monoid.CoprodI.lift_word_ping_pong`. When $k$ can be chosen with $k \ne i$ as well, $X_k$ and $X_i$ are disjoint and nonempty, so the image of $w$ is not $1$. In the remaining case, conjugate $w$ by a letter from a third factor, or by a well chosen element of a factor with three elements, to reach the first case. So no nonempty reduced word maps to $1$ (`Monoid.CoprodI.empty_of_word_prod_eq_one`), and the normal form gives injectivity. $\square$

The free group form is `FreeGroup.injective_lift_of_ping_pong`. Here each generator $a_i \in G$ comes with two sets $X_i$ and $Y_i$, all of them disjoint, such that $a_i \cdot (\alpha \setminus Y_i) \subseteq X_i$ and $a_i^{-1} \cdot (\alpha \setminus X_i) \subseteq Y_i$. Then the elements $a_i$ generate a free subgroup of $G$. The standard example is the pair of matrices $a = \begin{pmatrix} 1 & 2 \\ 0 & 1 \end{pmatrix}$ and $b = \begin{pmatrix} 1 & 0 \\ 2 & 1 \end{pmatrix}$ that act on $\mathbb{R}^2$. For $n \ne 0$, the matrix $a^n$ sends $(x, y)$ to $(x + 2ny, y)$, so it moves the set $|x| < |y|$ into the set $|x| > |y|$. In the same way $b^n$ moves the set $|x| > |y|$ into the set $|x| < |y|$. The lemma `Monoid.CoprodI.lift_injective_of_ping_pong`, applied to the two infinite cyclic groups that $a$ and $b$ generate, shows that $a$ and $b$ generate a free group.

The module also connects free products and free groups. The equivalence `freeGroupEquivCoprodI` says that the free group on $\iota$ is the free product of $\iota$ copies of the free group on one generator. The definition `Monoid.CoprodI.FreeGroupBasis.coprodI` says that the free product of free groups is free, with the union of the bases as a basis.

#### Common errors

1. `Monoid.Coprod M N` and the product `M × N` are different objects. In `M ∗ N` the elements $\mathrm{inl}(m)$ and $\mathrm{inr}(n)$ do not commute in general. The homomorphism `Monoid.Coprod.toProd` goes from the free product to the product, not back.
2. The library does not define `Monoid.Coprod M N` as `Monoid.CoprodI` of a family of two monoids. The two types have separate API, and no lemma of one applies to the other by unfolding.
3. The normal form `Monoid.CoprodI.Word.equiv` needs decidable equality on the index type and on each factor. In a classical proof, use the tactic *classical* first.

### Exercises

1. (A) Show that `Monoid.Coprod.fst` and `Monoid.Coprod.snd` are surjective, and compute their composites with `Monoid.Coprod.inl` and `Monoid.Coprod.inr`.
2. (A) Use `Monoid.Coprod.hom_ext` to prove that `Monoid.Coprod.swap N M` composed with `Monoid.Coprod.swap M N` is the identity.
3. (B) Let $a$ and $b$ be the generators of two copies of $\mathbb{Z}/2$. Show that $ab$ has infinite order in $\mathbb{Z}/2 * \mathbb{Z}/2$, with the normal form of reduced words.
4. (B) Prove that the free product of two nontrivial groups is not commutative.
5. (B) Show that the kernel of $\mathrm{toProd} : G * H \to G \times H$ is the normal subgroup generated by the commutators $[\mathrm{inl}(g), \mathrm{inr}(h)]$.
6. (C) Prove with the ping-pong lemma that the matrices $\begin{pmatrix} 1 & 2 \\ 0 & 1 \end{pmatrix}$ and $\begin{pmatrix} 1 & 0 \\ 2 & 1 \end{pmatrix}$ generate a free subgroup of $SL_2(\mathbb{Z})$.

### Reference

<?reference?>
