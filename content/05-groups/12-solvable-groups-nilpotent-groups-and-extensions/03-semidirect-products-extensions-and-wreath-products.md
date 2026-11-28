---
title: Semidirect products, extensions and wreath products
kind: api
modules:
  - Mathlib.GroupTheory.SemidirectProduct
  - Mathlib.GroupTheory.GroupExtension.Defs
  - Mathlib.GroupTheory.GroupExtension.Basic
  - Mathlib.GroupTheory.RegularWreathProduct
  - Mathlib.GroupTheory.Goursat
  - Mathlib.GroupTheory.NoncommCoprod
  - Mathlib.GroupTheory.NoncommPiCoprod
explains:
  E2: [SemidirectProduct.lift, SemidirectProduct.card, SemidirectProduct.range_inl_eq_ker_rightHom, SemidirectProduct.mulEquivSubgroup, GroupExtension.Section.exists_eq_inl_mul, GroupExtension.Splitting.semidirectProductMulEquiv, RegularWreathProduct.card, Subgroup.goursat, MonoidHom.noncommCoprod_injective, Subgroup.independent_of_coprime_order]
  E1: auto
families: []
requires: [V05.C02, V05.C04, V05.C05, V05.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Semidirect products, extensions and wreath products

### Overview

A normal subgroup $N$ of $E$ and the quotient $G = E/N$ do not determine $E$. The groups $\mathbb{Z}/4$ and $\mathbb{Z}/2 \times \mathbb{Z}/2$ both have a normal subgroup $\mathbb{Z}/2$ with quotient $\mathbb{Z}/2$. The data that connects $N$, $E$ and $G$ is a group extension, a short exact sequence $1 \to N \to E \to G \to 1$. When the projection $E \to G$ has a section that is a homomorphism, the extension splits, and $E$ is a semidirect product $N \rtimes G$. The direct product is the case of the trivial action.

This section describes seven modules. `Mathlib.GroupTheory.SemidirectProduct` builds $N \rtimes_\varphi G$ from an action $\varphi : G \to \operatorname{Aut}(N)$. The two modules `Mathlib.GroupTheory.GroupExtension.Defs` and `Mathlib.GroupTheory.GroupExtension.Basic` define extensions, sections and splittings, and prove that a split extension is a semidirect product. `Mathlib.GroupTheory.RegularWreathProduct` builds the wreath product $D \wr Q$, a semidirect product of $D^Q$ and $Q$. Three more modules treat products from the other side, as maps out of them: `Mathlib.GroupTheory.NoncommCoprod` and `Mathlib.GroupTheory.NoncommPiCoprod` give homomorphisms out of a product when the images commute, and `Mathlib.GroupTheory.Goursat` describes all subgroups of a product of two groups.

The section uses homomorphisms and automorphism groups from Chapter 2, complements of subgroups from Chapter 4, quotients from Chapter 5 and actions from Chapter 6.

### The library around it

#### Semidirect products

The type `SemidirectProduct N G φ` takes groups $N$, $G$ and a homomorphism `φ : G →* MulAut N`. The notation is `N ⋊[φ] G`. An element is a pair, with projections `SemidirectProduct.left` in $N$ and `SemidirectProduct.right` in $G$, and the product is
$$(n_1, g_1)(n_2, g_2) = (n_1 \cdot \varphi(g_1)(n_2),\ g_1 g_2).$$
This is `SemidirectProduct.mul_def`, and the projections of a product are `SemidirectProduct.mul_left` and `SemidirectProduct.mul_right`. The inverse is $(\varphi(g^{-1})(n^{-1}), g^{-1})$, by `SemidirectProduct.inv_left` and `SemidirectProduct.inv_right`. Two elements with the same projections are equal (`SemidirectProduct.ext`).

Three homomorphisms describe the structure. `SemidirectProduct.inl : N →* N ⋊[φ] G` sends $n$ to $(n, 1)$, `SemidirectProduct.inr : G →* N ⋊[φ] G` sends $g$ to $(1, g)$, and `SemidirectProduct.rightHom` sends $(n, g)$ to $g$. Both inclusions are injective (`SemidirectProduct.inl_injective`, `SemidirectProduct.inr_injective`), `SemidirectProduct.rightHom_surjective` holds, and the simp lemmas `SemidirectProduct.left_inl`, `SemidirectProduct.right_inr` and their relatives compute the projections. Each element is a product $(n, g) = \operatorname{inl}(n) \operatorname{inr}(g)$ (`SemidirectProduct.mk_eq_inl_mul_inr`). The action becomes conjugation: `SemidirectProduct.inl_aut` states
$$\operatorname{inl}(\varphi(g)(n)) = \operatorname{inr}(g)\, \operatorname{inl}(n)\, \operatorname{inr}(g)^{-1}.$$

**Proposition** (`SemidirectProduct.range_inl_eq_ker_rightHom`). The range of `inl` is the kernel of `rightHom`.

*Proof.* $(n, g)$ is in the kernel if and only if $g = 1$, that is, if and only if the element is $\operatorname{inl}(n)$. $\square$

So $N$ is a normal subgroup of $N \rtimes_\varphi G$ with quotient $G$.

**Proposition** (`SemidirectProduct.card`). $|N \rtimes_\varphi G| = |N| \cdot |G|$.

*Proof.* The function `SemidirectProduct.equivProd` is a bijection with $N \times G$, because the elements are pairs. Cardinality uses only the underlying set. $\square$

The universal property describes the homomorphisms out of the product.

**Proposition** (`SemidirectProduct.lift`). Let $f_N : N \to H$ and $f_G : G \to H$ be homomorphisms with $f_N(\varphi(g)(n)) = f_G(g)\, f_N(n)\, f_G(g)^{-1}$ for all $g$, $n$. Then $(n, g) \mapsto f_N(n) f_G(g)$ is a homomorphism $N \rtimes_\varphi G \to H$. It is the only homomorphism that restricts to $f_N$ and $f_G$.

*Proof.* Check the product rule: $f_N(n_1 \varphi(g_1)(n_2)) f_G(g_1 g_2) = f_N(n_1) f_G(g_1) f_N(n_2) f_G(g_1)^{-1} f_G(g_1) f_G(g_2)$, and the right side is $f_N(n_1) f_G(g_1) \cdot f_N(n_2) f_G(g_2)$. Uniqueness holds because each element is $\operatorname{inl}(n) \operatorname{inr}(g)$. $\square$

In Lean, the hypothesis is stated as an equality of homomorphisms with `MulAut.conj`. The restrictions are `SemidirectProduct.lift_inl` and `SemidirectProduct.lift_inr`, uniqueness is `SemidirectProduct.lift_unique`, and the extensionality lemma `SemidirectProduct.hom_ext` checks two homomorphisms on the images of `inl` and `inr`. The functorial map `SemidirectProduct.map` takes homomorphisms of both factors that are compatible with the actions, and `SemidirectProduct.congr` and `SemidirectProduct.congr'` give isomorphisms. For the trivial action, `SemidirectProduct.mulEquivProd` is the isomorphism `N ⋊[1] G ≃* N × G`.

The internal form starts from subgroups of one group $G$. If $K$ normalizes $H$, then `SemidirectProduct.monoidHomSubgroup` multiplies: it sends $(h, k)$ to $hk$, with $K$ acting on $H$ through `Subgroup.normalizerMonoidHom`. When $H$ is normal and $K$ is a complement of $H$ (`Subgroup.IsComplement'` of Chapter 4), this map is an isomorphism, `SemidirectProduct.mulEquivSubgroup`. Its proof is the definition of a complement: each $g$ is $hk$ in exactly one way.

#### Group extensions

A structure `GroupExtension N E G` has two homomorphisms, `GroupExtension.inl : N →* E` and `GroupExtension.rightHom : E →* G`, and three properties: `GroupExtension.inl_injective`, `GroupExtension.rightHom_surjective` and `GroupExtension.range_inl_eq_ker_rightHom`. The composite is trivial (`GroupExtension.rightHom_comp_inl`). The group $E$ acts on $N$ by conjugation through `GroupExtension.conjAct : E →* MulAut N`, and `GroupExtension.inl_conjAct_comm` states $\operatorname{inl}(e \cdot n) = e \operatorname{inl}(n) e^{-1}$. The quotient of $E$ by the kernel is $G$: this is `GroupExtension.quotientKerRightHomEquivRight`, and `GroupExtension.quotientRangeInlEquivRight` is the form with the range of `inl`.

Two extensions with the same $N$ and $G$ are equivalent, `GroupExtension.Equiv`, when an isomorphism $E \cong E'$ commutes with both maps. The equivalences form a groupoid with `GroupExtension.Equiv.refl`, `GroupExtension.Equiv.symm` and `GroupExtension.Equiv.trans`. The constructor `GroupExtension.Equiv.ofMonoidHom` needs only a homomorphism that commutes with both maps: it is then bijective, by the five lemma for groups.

A section, `GroupExtension.Section`, is a function $\sigma : G \to E$ with $\operatorname{rightHom} \circ \sigma = \operatorname{id}$, and `GroupExtension.surjInvRightHom` gives one by choice. A splitting, `GroupExtension.Splitting`, is a section that is a homomorphism. Each semidirect product is a split extension: `SemidirectProduct.toGroupExtension` gives the extension and `SemidirectProduct.inr_splitting` the splitting.

**Proposition** (`GroupExtension.Section.exists_eq_inl_mul`). Two sections $\sigma$, $\sigma'$ differ by $N$: for each $g$ there is $n \in N$ with $\sigma(g) = \operatorname{inl}(n)\, \sigma'(g)$.

*Proof.* Both $\sigma(g)$ and $\sigma'(g)$ map to $g$, so $\sigma(g) \sigma'(g)^{-1}$ is in the kernel of `rightHom`, which is the range of `inl`. $\square$

The module has the variants with the factor on the other side, such as `GroupExtension.Section.exists_eq_mul_inl`, and the membership forms such as `GroupExtension.Section.mul_inv_mem_range_inl`.

**Theorem** (`GroupExtension.Splitting.semidirectProductMulEquiv`). A splitting $s$ of $1 \to N \to E \to G \to 1$ gives an isomorphism $N \rtimes G \cong E$, where $G$ acts on $N$ by conjugation by $s(g)$.

*Proof.* The action is `GroupExtension.Splitting.conjAct`, and the map $(n, g) \mapsto \operatorname{inl}(n) s(g)$ satisfies the condition of `SemidirectProduct.lift`, by `GroupExtension.inl_conjAct_comm`. It is surjective: for $e \in E$, the proposition before gives $e = \operatorname{inl}(n)\, s(\operatorname{rightHom}(e))$ for some $n$. It is injective: if $\operatorname{inl}(n) s(g) = 1$, apply `rightHom` to get $g = 1$, and then $n = 1$ because `inl` is injective. $\square$

The stronger form `GroupExtension.Splitting.semidirectProductToGroupExtensionEquiv` says that the isomorphism is an equivalence of extensions. Two splittings are conjugate, `GroupExtension.IsConj`, when one is the conjugate of the other by an element $\operatorname{inl}(n)$. This is an equivalence relation, `GroupExtension.IsConj.setoid`, and its classes form the type `GroupExtension.ConjClasses`. The theorem of Schur and Zassenhaus in Chapter 8 is a statement of this kind for coprime orders.

#### Wreath products

For groups $D$ and $Q$, the regular wreath product `RegularWreathProduct D Q`, with notation `D ≀ᵣ Q`, has elements $(f, q)$ with $f : Q \to D$ and $q \in Q$. The projections are `RegularWreathProduct.left` and `RegularWreathProduct.right`, and the product is
$$(f_1, q_1)(f_2, q_2) = (x \mapsto f_1(x)\, f_2(q_1^{-1} x),\ q_1 q_2),$$
by `RegularWreathProduct.mul_left` and `RegularWreathProduct.mul_right`. So $Q$ acts on $D^Q$ by left translation of the argument. The homomorphism `RegularWreathProduct.rightHom` projects to $Q$, and `RegularWreathProduct.inl : Q →* D ≀ᵣ Q` is the inclusion of $Q$. Note the name: here `inl` is the inclusion of the acting group.

**Proposition** (`RegularWreathProduct.card`). If $Q$ is finite, then $|D \wr Q| = |D|^{|Q|} \cdot |Q|$.

*Proof.* `RegularWreathProduct.equivProd` is a bijection with $(Q \to D) \times Q$. $\square$

An action of $D$ on a set $\Lambda$ gives an action of $D \wr Q$ on $\Lambda \times Q$: `RegularWreathProduct.smul_def` states $(f, q) \cdot (\lambda, x) = (f(qx) \cdot \lambda,\ qx)$. The homomorphism `RegularWreathProduct.toPerm` into the permutations of $\Lambda \times Q$ is injective when the action of $D$ is faithful and $\Lambda$ is nonempty (`RegularWreathProduct.toPermInj`). The iterated wreath product `IteratedWreathProduct G n` has `IteratedWreathProduct_zero` and `IteratedWreathProduct_succ` as its recursion, and its order is $|G|^{1 + |G| + \dots + |G|^{n-1}}$ by `IteratedWreathProduct.card`. The main application is `Sylow.mulEquivIteratedWreathProduct`: a Sylow $p$-subgroup of the symmetric group on $p^n$ points is the $n$-fold iterated wreath product of a cyclic group of order $p$.

#### Products of commuting homomorphisms

Two homomorphisms $f : M \to P$ and $g : N \to P$ whose images commute elementwise give a homomorphism $M \times N \to P$, $(m, n) \mapsto f(m) g(n)$. This is `MonoidHom.noncommCoprod`, with the commuting hypothesis as an argument. The restrictions are `MonoidHom.noncommCoprod_comp_inl` and `MonoidHom.noncommCoprod_comp_inr`, and each homomorphism out of $M \times N$ is of this form (`MonoidHom.noncommCoprod_unique`). The range is the join of the two ranges (`MonoidHom.noncommCoprod_range`). `MulHom.noncommCoprod` is the version for semigroups.

**Proposition** (`MonoidHom.noncommCoprod_injective`). For groups, $(m, n) \mapsto f(m) g(n)$ is injective if and only if $f$ and $g$ are injective and their ranges are disjoint.

*Proof.* If $f(m) g(n) = f(m') g(n')$, then $f(m'^{-1} m) = g(n' n^{-1})$, by commutativity of the images. This element is in both ranges. With disjoint ranges it is $1$, and injectivity of $f$ and $g$ gives $m = m'$ and $n = n'$. The converse is direct. $\square$

The finite form `MonoidHom.noncommPiCoprod` takes a family $\phi_i : N_i \to M$ over a finite index type whose images commute pairwise, and multiplies: $(x_i) \mapsto \prod_i \phi_i(x_i)$. The product is well defined because the factors commute. It agrees with $\phi_i$ on `Pi.mulSingle` (`MonoidHom.noncommPiCoprod_mulSingle`), its range is the join of the ranges (`MonoidHom.noncommPiCoprod_range`), and `MonoidHom.noncommPiCoprodEquiv` is the bijection between commuting families and homomorphisms out of the product. It is injective when each $\phi_i$ is injective and the ranges are independent in the sense of `iSupIndep` (`MonoidHom.injective_noncommPiCoprod_of_iSupIndep`). For a family of subgroups $H_i$ of $G$, `Subgroup.noncommPiCoprod` is the multiplication map, with range $\bigsqcup_i H_i$ (`Subgroup.noncommPiCoprod_range`).

**Proposition** (`Subgroup.independent_of_coprime_order`). Let $H_i$ be finite subgroups of $G$ that commute pairwise, with pairwise coprime orders. Then the family is independent: each $H_i$ meets the join of the others only in $1$.

*Proof sketch.* The join $J$ of the $H_j$ with $j \ne i$ is the image of their product, so the order of each element of $J$ divides $\prod_{j \ne i} |H_j|$. An element of $H_i \cap J$ has order dividing $|H_i|$ and this product, which are coprime. So it is $1$. $\square$

With `Subgroup.injective_noncommPiCoprod_of_iSupIndep`, this gives the direct product decomposition of a finite nilpotent group into its Sylow subgroups.

#### The lemma of Goursat

The module `Mathlib.GroupTheory.Goursat` describes the subgroups $I$ of $G \times H$. The subgroup `Subgroup.goursatFst I` is $\{g \mid (g, 1) \in I\}$ (`Subgroup.mem_goursatFst`), and `Subgroup.goursatSnd I` is $\{h \mid (1, h) \in I\}$. Their product lies in $I$ (`Subgroup.goursatFst_prod_goursatSnd_le`). When both projections of $I$ are surjective, both subgroups are normal (`Subgroup.normal_goursatFst`, `Subgroup.normal_goursatSnd`), and `Subgroup.goursat_surjective` says that the image of $I$ in $G/I_1 \times H/I_2$ is the graph of an isomorphism.

**Theorem** (`Subgroup.goursat`). Each subgroup $I \le G \times H$ has the form: there are subgroups $G' \le G$, $H' \le H$, normal subgroups $M$ of $G'$ and $N$ of $H'$, and an isomorphism $e : G'/M \cong H'/N$, such that $I = \{(g, h) \in G' \times H' \mid e(gM) = hN\}$.

*Proof sketch.* Take $G'$ and $H'$ to be the two projections of $I$. Then $I$ is a subgroup of $G' \times H'$ with surjective projections, and the surjective case above gives $M$, $N$ and $e$. $\square$

The graph is `MonoidHom.graph` of $e$, pulled back along the product of the quotient maps and pushed into $G \times H$ along the inclusions.

#### Common errors

1. In `N ⋊[φ] G`, the action is `φ : G →* MulAut N`, a homomorphism into the automorphism group, not a `MulAction`. Write the action as a homomorphism first, for example with `MulAut.conj` for a conjugation action.
2. In the regular wreath product, `RegularWreathProduct.inl` is the inclusion of the acting group $Q$, while in the semidirect product `SemidirectProduct.inl` is the inclusion of the normal subgroup $N$. Read the type before you use either name.
3. `MonoidHom.noncommCoprod` and `MonoidHom.noncommPiCoprod` take the commuting hypothesis as an explicit argument. Lemmas about them, such as `MonoidHom.noncommPiCoprod_mulSingle`, need decidable equality on the index type.

### Exercises

1. (A) Show that the dihedral group of order $2n$ is a semidirect product $\mathbb{Z}/n \rtimes \mathbb{Z}/2$, with $\mathbb{Z}/2$ acting by inversion. Use `SemidirectProduct.mulEquivSubgroup`.
2. (A) Show that the extension $1 \to \mathbb{Z}/2 \to \mathbb{Z}/4 \to \mathbb{Z}/2 \to 1$ does not split.
3. (B) Show that $S_n \cong A_n \rtimes \mathbb{Z}/2$ for $n \ge 2$, with a transposition as the splitting.
4. (B) Show that $\mathbb{Z}/2 \wr \mathbb{Z}/2$ has order $8$ and is isomorphic to the dihedral group of order $8$.
5. (B) Use `Subgroup.goursat` to count the subgroups of $\mathbb{Z}/p \times \mathbb{Z}/p$ for a prime $p$.
6. (C) Let $G$ be finite and let $N$ be a normal subgroup with $\gcd(|N|, |G/N|) = 1$ and $N$ commutative. Show that any two splittings of $1 \to N \to G \to G/N \to 1$ are conjugate in the sense of `GroupExtension.IsConj`.

### Reference

<?reference?>
