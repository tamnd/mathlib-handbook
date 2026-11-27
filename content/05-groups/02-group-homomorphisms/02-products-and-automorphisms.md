---
title: Isomorphism classes, products and automorphisms
kind: theory
modules:
  - Mathlib.Algebra.Group.Prod
explains:
  E3: [MulAut.conj]
  E2: [MulAut, MulAut.conj_apply, MulEquiv.trans, MulEquiv.symm, MulEquiv.orderOf_eq, Prod.instGroup, MonoidHom.prod]
  E1: auto
families: []
requires: [V05.C01]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V05/C02/Examples.lean
  - MathlibHandbook/V05/C02/Exercises.lean
  - MathlibHandbook/V05/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Isomorphism classes, products and automorphisms

### Overview

Two isomorphic groups are the same group with other names for the elements. So a basic task of group theory is to decide when two groups are isomorphic. To show that they are, one writes down an isomorphism. To show that they are not, one finds a property that an isomorphism keeps and that one group has and the other has not. Such a property is an invariant. This section gives the first invariants: the number of elements, commutativity, and the number of solutions of $x^k = 1$.

The section also gives two constructions. The direct product $G \times H$ makes a new group from two groups. The theorem of the section in this direction is the Chinese remainder theorem for groups: $\mathbb{Z}/mn \cong \mathbb{Z}/m \times \mathbb{Z}/n$ if and only if $m$ and $n$ are coprime. The automorphisms of a group $G$ form a group $\operatorname{Aut}(G)$. Each element $g$ gives an automorphism, the conjugation $x \mapsto g x g^{-1}$, and this gives a homomorphism $G \to \operatorname{Aut}(G)$. The section ends with the computation $\operatorname{Aut}(\mathbb{Z}/n) \cong (\mathbb{Z}/n)^\times$.

### Definitions

**Definition (Direct product).** Let $G$ and $H$ be groups. The direct product $G \times H$ is the set of the pairs $(g, h)$ with the product $(g, h)(g', h') = (g g', h h')$. Its unit is $(1, 1)$, and the inverse of $(g, h)$ is $(g^{-1}, h^{-1})$.

Each axiom holds in $G \times H$ because it holds in each coordinate. The projections $(g, h) \mapsto g$ and $(g, h) \mapsto h$ are homomorphisms onto $G$ and onto $H$. The maps $g \mapsto (g, 1)$ and $h \mapsto (1, h)$ are injective homomorphisms. Their images commute with each other: $(g, 1)(1, h) = (g, h) = (1, h)(g, 1)$.

::: mathlib
`Prod.instGroup` · `Mathlib.Algebra.Group.Prod`

The product type `G × H` of Volume 1 has an instance of `Group` when `G` and `H` have one. The product of two pairs is computed in each coordinate, by the lemmas `Prod.fst_mul` and `Prod.snd_mul`.

<?decl Prod.instGroup?>
:::

::: mathlib
`MonoidHom.prod` · `Mathlib.Algebra.Group.Prod`

The universal property of the product: two homomorphisms `f : M →* N` and `g : M →* P` give `f.prod g : M →* N × P`, the map $x \mapsto (f(x), g(x))$. The projections are `MonoidHom.fst` and `MonoidHom.snd`, and the inclusions are `MonoidHom.inl` and `MonoidHom.inr`.

<?decl MonoidHom.prod?>
:::

**Definition (Automorphism group).** The automorphisms of a group $G$, the isomorphisms $G \to G$, form the set $\operatorname{Aut}(G)$. The product of two automorphisms is their composite.

::: mathlib
`MulAut` · `Mathlib.Algebra.Group.End`

The type `MulAut G` is `G ≃* G`, with a `Group` instance whose product is the composite. The convention of the product is the one of permutations: `(σ * τ) x = σ (τ x)`. The additive copy is `AddAut A`.

<?decl MulAut?>
:::

**Definition (Conjugation).** Let $G$ be a group and $g \in G$. Conjugation by $g$ is the map $c_g : G \to G$, $c_g(x) = g x g^{-1}$. An automorphism of the form $c_g$ is an inner automorphism.

**Definition (Center).** The center of $G$ is $Z(G) = \{ z \in G : z g = g z \text{ for each } g \in G \}$.

The center is all of $G$ exactly when $G$ is commutative. Chapter 5 studies the center as a subgroup.

### Theorems and proofs

**Theorem (Invariants of isomorphism).** Let $f : G \to H$ be an isomorphism. Then:

1. $G$ and $H$ have the same number of elements;
2. $G$ is commutative if and only if $H$ is commutative;
3. for each $k \in \mathbb{N}$, the map $f$ is a bijection from $\{a \in G : a^k = 1\}$ to $\{b \in H : b^k = 1\}$.

*Proof.* Claim 1 holds because $f$ is a bijection. For claim 2, assume $G$ is commutative and let $x, y \in H$. Write $x = f(a)$ and $y = f(b)$. Then $x y = f(a) f(b) = f(a b) = f(b a) = f(b) f(a) = y x$. The converse is the same argument for the isomorphism $f^{-1}$. For claim 3, $f(a)^k = f(a^k)$, so $a^k = 1$ implies $f(a)^k = f(1) = 1$. Conversely, if $f(a)^k = 1$, then $f(a^k) = 1 = f(1)$, and $f$ is injective, so $a^k = 1$. So $f$ maps the first set into the second, and it is injective. It is onto the second set, because each $b$ with $b^k = 1$ is $f(a)$ for $a = f^{-1}(b)$, and then $a^k = 1$ by the converse. $\square$

The least $n \ge 1$ with $a^n = 1$ is the order of $a$, the subject of Chapter 4. Claim 3 says that an isomorphism keeps the order of each element.

::: mathlib
`MulEquiv.orderOf_eq` · `Mathlib.GroupTheory.OrderOfElement`

An isomorphism keeps the order of each element: `orderOf (e x) = orderOf x`. The general form `orderOf_injective` needs only an injective homomorphism.

<?decl MulEquiv.orderOf_eq?>
:::

**Theorem (Isomorphism is an equivalence relation).** For groups $G$, $H$, $K$: $G \cong G$; if $G \cong H$ then $H \cong G$; if $G \cong H$ and $H \cong K$ then $G \cong K$.

*Proof.* The identity map is an isomorphism. The inverse of an isomorphism is an isomorphism, by the theorem of the previous section. The composite of two isomorphisms is a bijection and a homomorphism, so it is an isomorphism. $\square$

::: mathlib
`MulEquiv.symm` · `Mathlib.Algebra.Group.Equiv.Defs`

The inverse isomorphism. The lemmas `MulEquiv.apply_symm_apply` and `MulEquiv.symm_apply_apply` say that `e` and `e.symm` cancel.

<?decl MulEquiv.symm?>
:::

::: mathlib
`MulEquiv.trans` · `Mathlib.Algebra.Group.Equiv.Defs`

The composite of two isomorphisms. The order is the order of the arrows: `e₁.trans e₂ : G ≃* K` applies `e₁` first, unlike `MonoidHom.comp`. The lemma `MulEquiv.trans_apply` unfolds it.

<?decl MulEquiv.trans?>
:::

**Theorem (Chinese remainder theorem for groups).** Let $m, n \ge 1$. The additive groups $\mathbb{Z}/mn$ and $\mathbb{Z}/m \times \mathbb{Z}/n$ are isomorphic if and only if $\gcd(m, n) = 1$.

*Proof.* Assume $\gcd(m, n) = 1$. Define $\varphi : \mathbb{Z}/mn \to \mathbb{Z}/m \times \mathbb{Z}/n$ by $\varphi(a \bmod mn) = (a \bmod m, a \bmod n)$. The map is well defined: if $a \equiv a' \pmod{mn}$, then $m$ and $n$ both divide $a - a'$. It is a homomorphism, since reduction respects sums in each coordinate. It is injective: if $\varphi(a) = (0, 0)$, then $m \mid a$ and $n \mid a$, and since $m$ and $n$ are coprime, $mn \mid a$. So $\varphi(a) = \varphi(a')$ gives $\varphi(a - a') = 0$ and $a \equiv a' \pmod{mn}$. Both groups have $mn$ elements, so the injective map $\varphi$ is a bijection.

Assume $d = \gcd(m, n) > 1$, and let $L = mn/d$. Then $L$ is a multiple of $m$ and of $n$, so $L \cdot (x, y) = (0, 0)$ for each $(x, y) \in \mathbb{Z}/m \times \mathbb{Z}/n$. In $\mathbb{Z}/mn$ the element $1$ has $L \cdot 1 = L \neq 0$, because $0 < L < mn$. An isomorphism keeps the property "$L x = 0$ for each $x$", by claim 3 of the theorem on invariants in additive form. So the two groups are not isomorphic. $\square$

**Theorem (The automorphisms are a group).** For a group $G$, the set $\operatorname{Aut}(G)$ is a group under composition.

*Proof.* The composite of two automorphisms is an automorphism, by the equivalence relation above with $G = H = K$. Composition of maps is associative. The identity map is a unit. The inverse map of an automorphism is an automorphism, and it is an inverse in $\operatorname{Aut}(G)$. $\square$

**Theorem (Conjugation).** Let $G$ be a group. For each $g \in G$, the map $c_g$ is an automorphism of $G$. The map $c : G \to \operatorname{Aut}(G)$, $g \mapsto c_g$, is a homomorphism. The automorphism $c_g$ is the identity if and only if $g \in Z(G)$.

*Proof.* The map $c_g$ respects products:
$$c_g(x) c_g(y) = g x g^{-1} g y g^{-1} = g x y g^{-1} = c_g(x y).$$
It is a bijection with inverse $c_{g^{-1}}$, because $c_{g^{-1}}(c_g(x)) = g^{-1} g x g^{-1} g = x$, and the other composite is the same with $g$ and $g^{-1}$ exchanged. So $c_g$ is an automorphism. For the homomorphism, $c_g(c_h(x)) = g h x h^{-1} g^{-1} = (g h) x (g h)^{-1} = c_{g h}(x)$, by the inverse of a product. So $c_g \circ c_h = c_{g h}$. Last, $c_g = \mathrm{id}$ means $g x g^{-1} = x$ for each $x$. Multiply on the right by $g$: this is $g x = x g$ for each $x$, that is, $g \in Z(G)$. $\square$

::: mathlib
`MulAut.conj` · `Mathlib.Algebra.Group.End`

The homomorphism $c : G \to \operatorname{Aut}(G)$ as a bundled term `G →* MulAut G`. So `MulAut.conj g` is the automorphism $c_g$, and the theorem above is built into the type. The lemma `MulAut.conj_inv_apply` computes $c_g^{-1}(x) = g^{-1} x g$.

<?decl MulAut.conj?>
:::

::: mathlib
`MulAut.conj_apply` · `Mathlib.Algebra.Group.End`

The value $c_g(h) = g h g^{-1}$. It is a `simp` lemma. Note the side of the inverse: Mathlib conjugates as $g h g^{-1}$, not $g^{-1} h g$. The conjugation action of Chapter 6 uses the same convention.

<?decl MulAut.conj_apply?>
:::

**Theorem (Homomorphisms out of $\mathbb{Z}$).** Let $G$ be a group and $a \in G$. There is exactly one homomorphism $f : (\mathbb{Z}, +) \to G$ with $f(1) = a$, namely $f(n) = a^n$.

*Proof.* The map $f(n) = a^n$ is a homomorphism, because $a^{m+n} = a^m a^n$ by the laws of exponents in a group. It has $f(1) = a$. If $f'$ is another homomorphism with $f'(1) = a$, then $f'(n) = f'(n \cdot 1) = f'(1)^n = a^n$ by the theorem on powers, in additive form for the source. So $f' = f$. $\square$

**Theorem (Automorphisms of a cyclic group).** Let $n \ge 1$. The map $u \mapsto (x \mapsto u x)$ is an isomorphism $(\mathbb{Z}/n)^\times \to \operatorname{Aut}(\mathbb{Z}/n, +)$.

*Proof.* For $u \in \mathbb{Z}/n$ let $f_u(x) = u x$, with the product of the ring $\mathbb{Z}/n$. Each $f_u$ is a homomorphism of the additive group, since $u(x + y) = u x + u y$.

Step 1: each homomorphism $f$ of $(\mathbb{Z}/n, +)$ is $f_u$ for $u = f(1)$. Indeed, each $x \in \mathbb{Z}/n$ is $k \cdot 1$ for an integer $k$, and $f(k \cdot 1) = k f(1) = k u = u x$.

Step 2: $f_u$ is a bijection if and only if $u$ is a unit. If $u$ is a unit, then $f_{u^{-1}}$ is an inverse map of $f_u$, since $u^{-1}(u x) = x$. If $f_u$ is a bijection, then $1 = f_u(x) = u x$ for some $x$, so $u$ is a unit.

Step 3: the map $F(u) = f_u$ from $(\mathbb{Z}/n)^\times$ to $\operatorname{Aut}(\mathbb{Z}/n)$ is a homomorphism, because $f_u(f_v(x)) = u v x = f_{u v}(x)$. It is injective, because $f_u(1) = u$ recovers $u$. It is onto by steps 1 and 2. $\square$

### Examples

**Example (The isomorphism $\mathbb{Z}/6 \cong \mathbb{Z}/2 \times \mathbb{Z}/3$).** The map $\varphi$ of the Chinese remainder theorem sends
$$0 \mapsto (0,0), \quad 1 \mapsto (1,1), \quad 2 \mapsto (0,2), \quad 3 \mapsto (1,0), \quad 4 \mapsto (0,1), \quad 5 \mapsto (1,2).$$
The six images are distinct, so $\varphi$ is a bijection. For example $\varphi(2 + 5) = \varphi(1) = (1, 1)$, and $\varphi(2) + \varphi(5) = (0, 2) + (1, 2) = (1, 4) = (1, 1)$. In Mathlib the ring form of this isomorphism is `ZMod.chineseRemainder`, which takes a proof that $m$ and $n$ are coprime.

**Example (Two groups of order $4$).** The groups $\mathbb{Z}/4$ and $\mathbb{Z}/2 \times \mathbb{Z}/2$ both have four elements and are both commutative. They are not isomorphic. In $\mathbb{Z}/2 \times \mathbb{Z}/2$ each element $x$ satisfies $2 x = 0$, so the set $\{x : 2x = 0\}$ has four elements. In $\mathbb{Z}/4$ the solutions of $2 x = 0$ are $0$ and $2$ only. By claim 3 of the theorem on invariants, no isomorphism exists. This agrees with the Chinese remainder theorem, since $\gcd(2, 2) = 2$. The Klein four group of Chapter 1 and $(\mathbb{Z}/12)^\times$ are isomorphic to $\mathbb{Z}/2 \times \mathbb{Z}/2$.

**Example (Conjugation in $D_4$).** Take $g = s$ in $D_4$, with $s^{-1} = s$ and $r^i s = s r^{-i}$. Then
$$c_s(r) = s r s = s (s r^{-1}) = r^{-1} = r^3, \qquad c_s(s r) = s (s r) s = r s = s r^{-1} = s r^3.$$
So $c_s$ is not the identity, and $s \notin Z(D_4)$. The element $r^2$ commutes with $r$, and $r^2 s = s r^{-2} = s r^2$, so it commutes with $s$ too. Each element of $D_4$ is a product of powers of $r$ and $s$, so $r^2 \in Z(D_4)$. In fact $Z(D_4) = \{1, r^2\}$, as an exercise shows.

**Example (Automorphisms of $\mathbb{Z}$ and of $\mathbb{Z}/8$).** An automorphism of $(\mathbb{Z}, +)$ is determined by the image $u$ of $1$, by the theorem on homomorphisms out of $\mathbb{Z}$. It is the map $n \mapsto u n$, which is onto only for $u = \pm 1$. So $\operatorname{Aut}(\mathbb{Z}) = \{\mathrm{id}, -\mathrm{id}\}$ has two elements. For $\mathbb{Z}/8$, the theorem on cyclic groups gives $\operatorname{Aut}(\mathbb{Z}/8) \cong (\mathbb{Z}/8)^\times = \{1, 3, 5, 7\}$. The squares are $9 = 1$, $25 = 1$, $49 = 1$ modulo $8$, so this group is isomorphic to $\mathbb{Z}/2 \times \mathbb{Z}/2$, not to $\mathbb{Z}/4$.

**Counterexample (Inner automorphisms of a commutative group).** If $G$ is commutative, then $c_g(x) = g x g^{-1} = x$, so each inner automorphism is the identity. A commutative group can still have many automorphisms: $x \mapsto -x$ is an automorphism of $\mathbb{Z}/n$ that is not the identity for $n \ge 3$. So $\operatorname{Aut}(G)$ is in general larger than the image of $c$.

### The library around it

Isomorphisms have the constructors `MulEquiv.refl`, `MulEquiv.symm` and `MulEquiv.trans`, and the lemmas `MulEquiv.ext`, `MulEquiv.bijective`, `MulEquiv.injective` and `MulEquiv.surjective`. The product of groups has the isomorphisms `MulEquiv.prodComm` for $G \times H \cong H \times G$ and `MulEquiv.prodAssoc` for the associativity. The finite product of a family of groups is the type `(i : ι) → G i`, with the instance `Pi.group`.

The homomorphisms out of `ℤ` are classified by `zpowersHom`, an equivalence between `G` and `Multiplicative ℤ →* G`, and its additive form `zmultiplesHom`. The type tag `Multiplicative ℤ` is needed because `ℤ` is an additive group and `G` is a multiplicative one. Conjugation has two bundled forms: `MulAut.conj` as automorphisms, and the type `ConjAct G` of Chapter 6 as an action. The automorphisms that come from conjugation by elements of a normal subgroup are `MulAut.conjNormal`.

### Exercises

1. (A) Write the isomorphism $\mathbb{Z}/15 \to \mathbb{Z}/3 \times \mathbb{Z}/5$ on the elements $1$, $2$ and $7$.
2. (A) Show that $\mathbb{Z}/2 \times \mathbb{Z}/4$ and $\mathbb{Z}/8$ are not isomorphic.
3. (A) Show that $(\mathbb{Z}/5)^\times \cong \mathbb{Z}/4$. Hint: compute the powers of $2$ modulo $5$.
4. (B) Show that $Z(D_4) = \{1, r^2\}$. Hint: test $r^i$ against $s$, and $s r^i$ against $r$.
5. (B) Show that $G \times H \cong H \times G$, and that $G \times H$ is commutative if and only if $G$ and $H$ are.
6. (B) Show that an automorphism of the Klein four group $V$ is a permutation of the three elements $a, b, c$ other than $e$, and that each of the $6$ permutations gives an automorphism. Hint: the product of two distinct elements among $a, b, c$ is the third one.
7. (B) Show that $\mathbb{Q}$ and $\mathbb{Q} \times \mathbb{Q}$ are not isomorphic as additive groups. Hint: in $\mathbb{Q}$, any two elements are multiples of one element.
8. (C) Show that a group $G$ is commutative if and only if the map $c : G \to \operatorname{Aut}(G)$ is the trivial homomorphism, and that $\operatorname{Aut}(G)$ is trivial only if $G$ is commutative and $x = x^{-1}$ for each $x$.

### Notes and history

Cayley classified the groups of small order in his papers of 1854 and 1859, with tables, and he saw that there are two groups of order $4$. The Chinese remainder theorem is much older: it appears in the work of Sunzi in the third century, as a problem about remainders, and Gauss gave it its modern form. Hölder introduced the automorphism group of a group in 1893 and computed it for groups of small order. The distinction between inner and outer automorphisms is his.

In Mathlib, `MulAut` is in `Mathlib.Algebra.Group.End`, next to the endomorphisms and the permutations, because the three share the convention for the product. The products of monoids and groups are in `Mathlib.Algebra.Group.Prod`, which was written in Lean 3 with the bundled homomorphisms `fst`, `snd`, `inl`, `inr` and `prod`.

### Reference

<?reference?>
