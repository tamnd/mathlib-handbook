---
title: HNN extensions and amalgamated products
kind: api
modules:
  - Mathlib.GroupTheory.HNNExtension
  - Mathlib.GroupTheory.PushoutI
explains:
  E2: [HNNExtension.lift, HNNExtension.of_injective, HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range, Monoid.PushoutI.lift, Monoid.PushoutI.of_injective, Monoid.PushoutI.inf_of_range_eq_base_range]
  E1: auto
families: []
requires: [V01, V05.C01, V05.C02, V05.C03, V05.C04, V05.C05, V05.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## HNN extensions and amalgamated products

### Overview

Two constructions of combinatorial group theory build a large group from smaller groups and a set of identifications. The amalgamated product $G_1 *_H G_2$ glues two groups along a common subgroup $H$. It is the pushout of the diagram $G_1 \leftarrow H \to G_2$ in the category of groups. The HNN extension of a group $G$ along an isomorphism $\varphi : A \to B$ of two subgroups adds one new element $t$ with $t a t^{-1} = \varphi(a)$ for each $a \in A$. Both constructions contain a copy of the groups that they start from, and both have a normal form theorem for their elements. In topology they are the fundamental groups of a space glued from two pieces, and of a space with a handle glued on.

The module `Mathlib.GroupTheory.PushoutI` defines the pushout of a family of monoids over a common base, and proves the normal form theorem for amalgamated products of groups. The module `Mathlib.GroupTheory.HNNExtension` defines HNN extensions and proves their normal form theorem and Britton's lemma. Both modules build on the free products of Section 1 of this chapter, on transversals of cosets from Chapter 4, and on group actions from Chapter 6, which give the proofs of the normal forms.

### The library around it

#### The pushout of a family

Let $(G_i)_{i \in \iota}$ be a family of monoids, $H$ a monoid, and $\varphi_i : H \to G_i$ homomorphisms. The type `Monoid.PushoutI φ` is the quotient of the free product of `Monoid.CoprodI G` and $H$ by the congruence `Monoid.PushoutI.con`. This congruence identifies $\varphi_i(h)$ in the factor $G_i$ with $h$ in the factor $H$, for each $i$ and $h$. The monoid structure is `Monoid.PushoutI.monoid`, and for groups `Monoid.PushoutI.instGroup` gives a group. The maps into the pushout are `Monoid.PushoutI.of i : G i →* PushoutI φ` and `Monoid.PushoutI.base φ : H →* PushoutI φ`. The square commutes: `Monoid.PushoutI.of_comp_eq_base` says $\mathrm{of}_i \circ \varphi_i = \mathrm{base}$, and `Monoid.PushoutI.of_apply_eq_base` is the form for one element. The map `Monoid.PushoutI.ofCoprodI` sends the free product of the $G_i$ to the pushout.

**The universal property.** Let $K$ be a monoid, $f_i : G_i \to K$ homomorphisms and $k : H \to K$ a homomorphism with $f_i \circ \varphi_i = k$ for each $i$. Then `Monoid.PushoutI.lift f k hf` is the unique homomorphism $F$ out of the pushout with $F \circ \mathrm{of}_i = f_i$ and $F \circ \mathrm{base} = k$.

*Proof.* The maps $f_i$ give a homomorphism out of the free product of the $G_i$ by `Monoid.CoprodI.lift`, and with $k$ they give a homomorphism $\Phi$ out of the free product with $H$ by `Monoid.Coprod.lift`. The hypothesis says that $\Phi$ takes the same value on $\varphi_i(h)$ and on $h$. So $\Phi$ is constant on the classes of the congruence that these pairs generate, and it goes down to the quotient. Uniqueness holds because the images of the maps $\mathrm{of}_i$ and $\mathrm{base}$ generate the pushout. $\square$

The computation rules are `Monoid.PushoutI.lift_of` and `Monoid.PushoutI.lift_base`. The extensionality lemma `Monoid.PushoutI.hom_ext` compares two homomorphisms on each $G_i$ and on $H$. When $\iota$ is nonempty, the base is the image of some $G_i$, and `Monoid.PushoutI.hom_ext_nonempty` needs only the maps $\mathrm{of}_i$. The equivalence `Monoid.PushoutI.homEquiv` packs the universal property as a bijection between homomorphisms out of the pushout and compatible families. The principle `Monoid.PushoutI.induction_on` proves a statement for all elements from the cases $\mathrm{of}_i\,g$, $\mathrm{base}\,h$ and products.

#### The normal form of the amalgamated product

From here on, the $G_i$ and $H$ are groups and each $\varphi_i$ is injective. Then the pushout is the amalgamated product of the $G_i$ over the subgroup $H$. A normal form needs a choice of coset representatives. A transversal, the structure `Monoid.PushoutI.NormalWord.Transversal φ`, chooses for each $i$ a set of representatives of the right cosets of $\varphi_i(H)$ in $G_i$, with the representative $1$ for the subgroup itself. The field `Monoid.PushoutI.NormalWord.Transversal.compl` states this with `Subgroup.IsComplement` of Chapter 4. A transversal exists when the maps are injective (`Monoid.PushoutI.NormalWord.transversal_nonempty`).

A normal word, `Monoid.PushoutI.NormalWord d`, is an element $h$ of $H$ and a reduced word $g_1 g_2 \cdots g_n$ of the free product, with each letter $g_k$ in the chosen transversal of its factor. It stands for the product $h\,g_1 \cdots g_n$, with the function `Monoid.PushoutI.NormalWord.prod`.

**Normal form theorem.** Each element of the amalgamated product is the product of exactly one normal word. The equivalence is `Monoid.PushoutI.NormalWord.equiv`, and `Monoid.PushoutI.NormalWord.prod_injective` is the uniqueness.

*Proof sketch.* The proof has the same plan as for the free product in Section 1. Each $G_i$ acts on normal words: to compute $g \cdot w$, multiply $g$ with the first letter of $w$ when it comes from $G_i$, and write the result as an element of $\varphi_i(H)$ times a representative. The equivalence `Monoid.PushoutI.NormalWord.equivPair` does this split, and `Monoid.PushoutI.NormalWord.summandAction` is the action. The group $H$ acts on the head, by `Monoid.PushoutI.NormalWord.baseAction`. The actions agree on $H$, so the universal property combines them into an action of the pushout. Then `Monoid.PushoutI.NormalWord.prod_smul` says that the product of $g \cdot w$ is $g$ times the product of $w$, and `Monoid.PushoutI.NormalWord.prod_smul_empty` says that $\mathrm{prod}(w) \cdot \mathrm{empty} = w$. So $g \mapsto g \cdot \mathrm{empty}$ is inverse to the product. $\square$

The consequences are the facts that make the amalgamated product useful.

**Injectivity.** If each $\varphi_i$ is injective, then each map $\mathrm{of}_i : G_i \to G_1 *_H G_2$ is injective (`Monoid.PushoutI.of_injective`), and the base map is injective (`Monoid.PushoutI.base_injective`).

*Proof.* Let $g \in G_i$, and compute $g \cdot \mathrm{empty}$. Write $g = \varphi_i(h)\,s$ with $s$ a representative. The normal word $g \cdot \mathrm{empty}$ has head $h$ and the one letter $s$, or no letter when $s = 1$. So the normal word determines $h$ and $s$, and so $g$. Two elements with the same image in the pushout act in the same way, so they are equal. $\square$

**Intersection of the factors.** For $i \ne j$, the images of $G_i$ and $G_j$ meet exactly in the image of $H$. This is `Monoid.PushoutI.inf_of_range_eq_base_range`.

*Proof sketch.* The image of $H$ is in both images by the commuting square. Conversely, let $x = \mathrm{of}_i(g_1) = \mathrm{of}_j(g_2)$. If $g_1 \notin \varphi_i(H)$, the normal word of $x$ has one letter, from $G_i$. If $g_2 \notin \varphi_j(H)$, it has one letter, from $G_j$. The normal form is unique and $i \ne j$, so one of $g_1$ and $g_2$ lies in the image of $H$, and then $x$ lies in the image of $H$. $\square$

The predicate `Monoid.PushoutI.Reduced` says that no letter of a word of the free product is in the image of $H$. The lemma `Monoid.PushoutI.Reduced.exists_normalWord_prod_eq` turns a reduced word into a normal word with the same product and the same sequence of factors. So a nonempty reduced word does not have its product in the image of $H$, and so it is not $1$.

#### HNN extensions

Let $G$ be a group, $A$ and $B$ subgroups, and $\varphi : A \cong B$ an isomorphism. The type `HNNExtension G A B φ` is the quotient of the free product $G * \mathbb{Z}$ by the congruence `HNNExtension.con`. Write $t$ for the generator of $\mathbb{Z}$. The congruence identifies $t\,a$ with $\varphi(a)\,t$ for each $a \in A$. The group instance is `instGroupHNNExtension`, the map from $G$ is `HNNExtension.of`, and the new element is `HNNExtension.t`.

The defining relation has four forms, for the two sides and for $t$ and $t^{-1}$.

| Lean name | Statement |
|---|---|
| `HNNExtension.t_mul_of` | $t\,a = \varphi(a)\,t$ for $a \in A$ |
| `HNNExtension.equiv_eq_conj` | $\varphi(a) = t\,a\,t^{-1}$ for $a \in A$ |
| `HNNExtension.of_mul_t` | $b\,t = t\,\varphi^{-1}(b)$ for $b \in B$ |
| `HNNExtension.equiv_symm_eq_conj` | $\varphi^{-1}(b) = t^{-1}\,b\,t$ for $b \in B$ |
| `HNNExtension.inv_t_mul_of` | $t^{-1}\,b = \varphi^{-1}(b)\,t^{-1}$ for $b \in B$ |
| `HNNExtension.of_mul_inv_t` | $a\,t^{-1} = t^{-1}\,\varphi(a)$ for $a \in A$ |

**The universal property.** Let $f : G \to H$ be a homomorphism and $x \in H$ with $x\,f(a) = f(\varphi(a))\,x$ for each $a \in A$. Then `HNNExtension.lift f x hx` is the homomorphism out of the HNN extension that is $f$ on $G$ and sends $t$ to $x$.

*Proof.* The homomorphism `Monoid.Coprod.lift` of $f$ and of $n \mapsto x^n$ is defined on $G * \mathbb{Z}$. The hypothesis says that it takes the same value on $t\,a$ and on $\varphi(a)\,t$. So it goes down to the quotient by the congruence. $\square$

The computation rules are `HNNExtension.lift_of` and `HNNExtension.lift_t`. Two homomorphisms are equal when they agree on $G$ and on $t$ (`HNNExtension.hom_ext`). The principle `HNNExtension.induction_on` proves a statement for all elements from the cases $\mathrm{of}\,g$, $t$, products and inverses.

#### The normal form and Britton's lemma

The two subgroups play symmetric parts, so the library indexes them by the units $\pm 1$ of $\mathbb{Z}$. The function `HNNExtension.toSubgroup A B u` is $A$ for $u = 1$ (`HNNExtension.toSubgroup_one`) and $B$ for $u = -1$ (`HNNExtension.toSubgroup_neg_one`). The isomorphism `HNNExtension.toSubgroupEquiv` is $\varphi$ for $u = 1$ and $\varphi^{-1}$ for $u = -1$. A transversal pair, `HNNExtension.NormalWord.TransversalPair G A B`, chooses representatives of the cosets of $A$ and of $B$ in $G$. One exists for each pair of subgroups (`HNNExtension.NormalWord.TransversalPair.nonempty`).

A reduced word, `HNNExtension.NormalWord.ReducedWord G A B`, is an element $g_0$ of $G$ and a list of pairs $(u_k, g_k)$ with $u_k = \pm 1$, for the product $g_0\,t^{u_1} g_1 \cdots t^{u_n} g_n$. The product is `HNNExtension.NormalWord.ReducedWord.prod`. The condition `HNNExtension.NormalWord.ReducedWord.chain` forbids a pinch: a part $t^{u}\,g\,t^{-u}$ with $g$ in the subgroup of index $u$. A pinch can always be removed with the defining relation, and the result is a shorter word for the same element. A normal word, `HNNExtension.NormalWord d`, is a reduced word in which each $g_k$ is in the chosen transversal.

**Normal form theorem.** Each element of the HNN extension is the product of exactly one normal word. The bijection is `HNNExtension.NormalWord.equiv`, and `HNNExtension.NormalWord.prod_injective` is the uniqueness.

*Proof sketch.* The group $G$ acts on normal words by multiplication of the head. The element $t^u$ acts by `HNNExtension.NormalWord.unitsSMul`: it puts $t^u$ in front of the word and moves the head through it with the isomorphism `HNNExtension.toSubgroupEquiv`, or it cancels a pinch when one appears. The predicate `HNNExtension.NormalWord.Cancels` tells the two cases apart, and `HNNExtension.NormalWord.unitsSMulEquiv` shows that the action of $t^u$ is a bijection. These actions satisfy the defining relation, so `HNNExtension.lift` combines them into an action of the HNN extension on normal words. As for the amalgamated product, $g \mapsto g \cdot \mathrm{empty}$ is the inverse of the product (`HNNExtension.NormalWord.prod_smul_empty`). $\square$

**The base group embeds.** The map $\mathrm{of} : G \to$ `HNNExtension G A B φ` is injective. This is `HNNExtension.of_injective`.

*Proof.* The action of $\mathrm{of}\,g$ on the empty normal word gives the normal word with head $g$ and an empty list (`HNNExtension.NormalWord.ofGroup`). Different elements of $G$ give different words. $\square$

**Britton's lemma.** If the product of a reduced word lies in the image of $G$, then the word has no letter $t^{\pm 1}$. This is `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`.

*Proof sketch.* By `HNNExtension.ReducedWord.exists_normalWord_prod_eq`, the reduced word has a normal word with the same product and the same sequence of exponents $u_k$. An element $\mathrm{of}\,g$ has the normal word with an empty list. Uniqueness of the normal form gives an empty list for the normal word, and so for the reduced word. $\square$

The lemma `HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq` is the stronger form: two reduced words with the same product have the same sequence of exponents.

#### Common errors

1. `Monoid.PushoutI φ` is defined for any family of homomorphisms, not only injective ones. The injectivity theorems `Monoid.PushoutI.of_injective` and `Monoid.PushoutI.base_injective` take the injectivity of each $\varphi_i$ as a hypothesis. Without it the base map can have a kernel.
2. The defining relation of `HNNExtension G A B φ` is $t\,a\,t^{-1} = \varphi(a)$, with $t$ on the left. Some books use $t^{-1} a\,t = \varphi(a)$. Check the side before using `HNNExtension.t_mul_of` or `HNNExtension.of_mul_t`.
3. The amalgamated product of two groups is `Monoid.PushoutI` over an index type with two elements. The library has no separate type for two factors, and a statement for $G_1 *_H G_2$ needs a family indexed by this type.

### Exercises

1. (A) Use `HNNExtension.lift` to build a homomorphism from `HNNExtension G A B φ` onto $\mathbb{Z}$ that kills $G$ and sends $t$ to $1$, and deduce that $t$ has infinite order.
2. (A) Show with `Monoid.PushoutI.hom_ext` that a pushout over the trivial group $H$ has the universal property of the free product `Monoid.CoprodI G`.
3. (B) Let $G = \mathbb{Z}$, $A = B = G$ and $\varphi = -\mathrm{id}$. Show that the HNN extension is the fundamental group of the Klein bottle, with the presentation $\langle a, t \mid t a t^{-1} = a^{-1} \rangle$, and that it is not commutative.
4. (B) Let $G = \mathbb{Z}$, $A = 2\mathbb{Z}$, $B = 3\mathbb{Z}$, and $\varphi(2n) = 3n$. Use Britton's lemma to show that the element $t a t^{-1} a^{-1}$, with $a$ the generator of $G$, is not $1$.
5. (B) Use `Monoid.PushoutI.lift` to build a homomorphism from the amalgamated product $\mathbb{Z}/4 *_{\mathbb{Z}/2} \mathbb{Z}/6$ onto $SL_2(\mathbb{Z})$. Send the generators to the matrices $S$ and $ST$ of orders $4$ and $6$, and check that $S^2 = (ST)^3 = -1$ gives the compatibility on $\mathbb{Z}/2$.
6. (C) Prove that a nonempty reduced word in an amalgamated product over injective maps has a product different from $1$, with `Monoid.PushoutI.Reduced.exists_normalWord_prod_eq`.

### Reference

<?reference?>
