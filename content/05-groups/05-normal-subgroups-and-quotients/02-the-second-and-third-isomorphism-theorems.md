---
title: The second and third isomorphism theorems and the correspondence theorem
kind: theory
modules:
  - Mathlib.GroupTheory.QuotientGroup.Basic
explains:
  E3: [QuotientGroup.quotientInfEquivProdNormalQuotient, QuotientGroup.quotientQuotientEquivQuotient]
  E2: [QuotientGroup.comapMk'OrderIso, Subgroup.mul_normal, QuotientGroup.map, Subgroup.comap_map_eq, Subgroup.Normal.comap, Subgroup.subgroupOf]
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

## The second and third isomorphism theorems and the correspondence theorem

### Overview

The first isomorphism theorem identifies the image of a homomorphism. The second and the third theorems are consequences of it. They describe the quotients that appear when a group has two subgroups. The second theorem compares $H/(H \cap N)$ with $H N / N$. The third theorem says that a quotient of a quotient is a quotient: $(G/N)/(M/N) \cong G/M$. The correspondence theorem describes all the subgroups of $G/N$: they are the subgroups $K/N$ with $N \le K \le G$.

Each proof follows the same plan: give a surjective homomorphism, compute its kernel, and apply the first isomorphism theorem. Chapter 8 uses the correspondence theorem in the proof of the first Sylow theorem.

### Definitions

**Definition (Product set).** For subgroups $H, N \le G$, the product set is $H N = \{h n : h \in H, n \in N\}$.

**Definition (Subgroup of a subgroup).** Let $N, H \le G$. The intersection $H \cap N$ is a subgroup of the group $H$. Mathlib writes it as a subgroup of the type `↥H`.

::: mathlib
`Subgroup.subgroupOf` · `Mathlib.Algebra.Group.Subgroup.Map`

The term `N.subgroupOf H : Subgroup ↥H` is $H \cap N$ seen inside $H$: the preimage of `N` under the inclusion `↥H → G`. When `N` is normal in `G`, the instance `Subgroup.normal_subgroupOf` makes it normal in `↥H`.

<?decl Subgroup.subgroupOf?>
:::

**Definition (Image of a quotient).** Let $N \le M$ be normal subgroups of $G$. The set $M/N = \{m N : m \in M\}$ is the image of $M$ under the quotient map $\pi : G \to G/N$.

### Theorems and proofs

**Lemma (Product with a normal subgroup).** Let $H \le G$ and $N \trianglelefteq G$. Then $H N$ is a subgroup, $H N = N H$, and $H N$ is the join $H \sqcup N$.

*Proof.* For $h \in H$ and $n \in N$, $h n = (h n h^{-1}) h \in N H$, and $n h = h (h^{-1} n h) \in H N$, by normality. So $H N = N H$. It contains $1 = 1 \cdot 1$. Products: $(h n)(h' n') = h h' (h'^{-1} n h') n' \in H N$. Inverses: $(h n)^{-1} = n^{-1} h^{-1} \in N H = H N$. So $H N$ is a subgroup. It contains $H$ and $N$, and each subgroup that contains $H$ and $N$ contains all products $h n$. So $H N$ is the least subgroup that contains both. $\square$

::: mathlib
`Subgroup.mul_normal` · `Mathlib.Algebra.Group.Subgroup.Pointwise`

The lemma as an equation of sets: `↑(H ⊔ N) = ↑H * ↑N`, where the right side is the pointwise product. The join of two normal subgroups is normal, by the instance `Subgroup.sup_normal`.

<?decl Subgroup.mul_normal?>
:::

**Theorem (Second isomorphism theorem).** Let $H \le G$ and $N \trianglelefteq G$. Then $H \cap N \trianglelefteq H$, and
$$H / (H \cap N) \cong H N / N.$$

*Proof.* The subgroup $N$ is normal in $H N$, since it is normal in $G$. Define $\varphi : H \to H N / N$ by $\varphi(h) = h N$. It is the restriction of the quotient map to $H$, so it is a homomorphism. It is onto: an element of $H N / N$ is $h n N$ with $h \in H$ and $n \in N$, and $h n N = h N = \varphi(h)$. Its kernel is the set of the $h \in H$ with $h N = N$, that is, $h \in N$. So $\ker \varphi = H \cap N$. A kernel is normal, so $H \cap N \trianglelefteq H$, and the first isomorphism theorem gives $H/(H \cap N) \cong H N / N$. $\square$

**Corollary (Order of a product).** If $H$ and $N$ are finite and $N$ is normal, then $|H N| = |H| \, |N| / |H \cap N|$.

*Proof.* By the theorem and Lagrange's theorem, $|H|/|H \cap N| = |H N|/|N|$. $\square$

The count holds for any two finite subgroups $H$ and $K$, normal or not, as an exercise shows. But then $H K$ need not be a subgroup.

::: mathlib
`QuotientGroup.quotientInfEquivProdNormalQuotient` · `Mathlib.GroupTheory.QuotientGroup.Basic`

The second isomorphism theorem: `↥H ⧸ N.subgroupOf H ≃* ↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)`. Both sides are quotients of subgroups, so both use `subgroupOf`. The join `H ⊔ N` is $H N$ by the lemma.

<?decl QuotientGroup.quotientInfEquivProdNormalQuotient?>
:::

**Theorem (Third isomorphism theorem).** Let $N \le M$ be normal subgroups of $G$. Then $M/N$ is a normal subgroup of $G/N$, and
$$(G/N)/(M/N) \cong G/M.$$

*Proof.* Let $\pi_M : G \to G/M$ be the quotient map. Its kernel $M$ contains $N$, so by the universal property there is a homomorphism $\psi : G/N \to G/M$ with $\psi(g N) = g M$. It is onto, because $\pi_M$ is onto. Its kernel is the set of the classes $g N$ with $g M = M$, that is, $g \in M$. So $\ker \psi = \{g N : g \in M\} = M/N$. A kernel is normal, and the first isomorphism theorem gives $(G/N)/(M/N) \cong G/M$. $\square$

::: mathlib
`QuotientGroup.map` · `Mathlib.GroupTheory.QuotientGroup.Defs`

A homomorphism `f : G →* H` with `N ≤ M.comap f` gives `G ⧸ N →* H ⧸ M`, $g N \mapsto f(g) M$. The map $\psi$ of the proof is `QuotientGroup.map N M (MonoidHom.id G) h`.

<?decl QuotientGroup.map?>
:::

::: mathlib
`QuotientGroup.quotientQuotientEquivQuotient` · `Mathlib.GroupTheory.QuotientGroup.Basic`

The third isomorphism theorem: `(G ⧸ N) ⧸ (M.map (mk' N)) ≃* G ⧸ M` for `N ≤ M`. The subgroup $M/N$ is written as the image `M.map (QuotientGroup.mk' N)`.

<?decl QuotientGroup.quotientQuotientEquivQuotient?>
:::

**Theorem (Correspondence theorem).** Let $N \trianglelefteq G$ and $\pi : G \to G/N$. The maps $K \mapsto \pi(K) = K/N$ and $L \mapsto \pi^{-1}(L)$ are inverse bijections between the subgroups $K$ of $G$ with $N \le K$ and the subgroups $L$ of $G/N$. They keep inclusion and normality. If $G$ is finite, then $[G : K] = [G/N : K/N]$.

*Proof.* The image and the preimage of a subgroup are subgroups, by Chapter 3. The preimage $\pi^{-1}(L)$ contains $N = \pi^{-1}(\{1\})$.

Inverse bijections. Let $L \le G/N$. Since $\pi$ is onto, $\pi(\pi^{-1}(L)) = L$. Let $N \le K \le G$. Then $K \subseteq \pi^{-1}(\pi(K))$. Conversely, if $\pi(g) \in \pi(K)$, then $\pi(g) = \pi(k)$ for some $k \in K$. So $k^{-1} g \in N \le K$, and $g = k (k^{-1} g) \in K$. So $\pi^{-1}(\pi(K)) = K$.

Inclusion. Image and preimage keep inclusion, and they are inverse to each other, so $K_1 \le K_2$ if and only if $K_1/N \le K_2/N$.

Normality. If $L \trianglelefteq G/N$, then $\pi^{-1}(L)$ is normal: for $k \in \pi^{-1}(L)$, $\pi(g k g^{-1}) = \pi(g) \pi(k) \pi(g)^{-1} \in L$. If $K \trianglelefteq G$, then $K/N$ is normal: each element of $G/N$ is some $\pi(g)$, and $\pi(g) \pi(k) \pi(g)^{-1} = \pi(g k g^{-1}) \in \pi(K)$.

Index. By Lagrange's theorem, $[G/N : K/N] = |G/N|/|K/N| = (|G|/|N|)/(|K|/|N|) = |G|/|K|$. $\square$

::: mathlib
`QuotientGroup.comapMk'OrderIso` · `Mathlib.GroupTheory.QuotientGroup.Basic`

The correspondence theorem as an order isomorphism: `Subgroup (G ⧸ N) ≃o Set.Ici N`. The right side is the set of the subgroups `K` with `N ≤ K`, ordered by inclusion. The forward map is the preimage under `mk' N`.

<?decl QuotientGroup.comapMk'OrderIso?>
:::

::: mathlib
`Subgroup.comap_map_eq` · `Mathlib.Algebra.Group.Subgroup.Ker`

The general form of the step $\pi^{-1}(\pi(K)) = K$: for each homomorphism `f`, `(H.map f).comap f = H ⊔ f.ker`. For `N ≤ K` and `f = mk' N` the join is `K`. The dual lemma is `Subgroup.map_comap_eq`, with `f.range ⊓ H`.

<?decl Subgroup.comap_map_eq?>
:::

::: mathlib
`Subgroup.Normal.comap` · `Mathlib.Algebra.Group.Subgroup.Basic`

The preimage of a normal subgroup under any homomorphism is normal. For the image the lemma `Subgroup.Normal.map` needs a surjective map.

<?decl Subgroup.Normal.comap?>
:::

### Examples

**Example (The theorems in $\mathbb{Z}$).** Take $H = 4\mathbb{Z}$ and $N = 6\mathbb{Z}$. Then $H + N = 2\mathbb{Z}$ and $H \cap N = 12\mathbb{Z}$, by Chapter 3. The second theorem gives $4\mathbb{Z}/12\mathbb{Z} \cong 2\mathbb{Z}/6\mathbb{Z}$, and both groups have order $3$. For the third theorem take $N = 12\mathbb{Z} \le M = 4\mathbb{Z}$: then $(\mathbb{Z}/12)/(4\mathbb{Z}/12\mathbb{Z}) \cong \mathbb{Z}/4$. The correspondence theorem matches the subgroups of $\mathbb{Z}/12$ with the subgroups $d\mathbb{Z} \supseteq 12\mathbb{Z}$, that is, with the divisors $d$ of $12$, as Chapter 3 found.

**Example ($S_4$ modulo the Klein group).** Let $V = \{e, (1\,2)(3\,4), (1\,3)(2\,4), (1\,4)(2\,3)\} \le S_4$. For $\sigma \in S_4$ and a transposition, $\sigma (a\,b) \sigma^{-1} = (\sigma(a)\,\sigma(b))$, since both sides exchange $\sigma(a)$ and $\sigma(b)$ and fix the other points. So $\sigma (a\,b)(c\,d) \sigma^{-1} = (\sigma(a)\,\sigma(b))(\sigma(c)\,\sigma(d))$ is again a product of two disjoint transpositions. So $V$ is normal. Let $H \cong S_3$ be the stabilizer of the point $4$. Each element of $V$ other than $e$ moves $4$, so $H \cap V = \{e\}$. By the corollary, $|H V| = 6 \cdot 4 / 1 = 24$, so $H V = S_4$. The second theorem gives $S_4 / V \cong H/\{e\} \cong S_3$.

**Example (Subgroups of $D_4$ that contain the center).** Let $Z = \{1, r^2\} \le D_4$. The last section showed $D_4/Z \cong \mathbb{Z}/2 \times \mathbb{Z}/2$, a group with $5$ subgroups. By the correspondence theorem, $D_4$ has exactly $5$ subgroups that contain $Z$: $Z$, $\{1, r, r^2, r^3\}$, $\{1, r^2, s, s r^2\}$, $\{1, r^2, s r, s r^3\}$ and $D_4$. They all have index $1$, $2$ or $4$, and the three of index $2$ are normal.

**Counterexample (A product of subgroups that is not a subgroup).** In $S_3$ let $H = \{e, (1\,2)\}$ and $K = \{e, (1\,3)\}$. Neither is normal. The set $H K = \{e, (1\,2), (1\,3), (1\,2)(1\,3)\}$ has $4 = 2 \cdot 2 / 1$ elements. A subgroup of $S_3$ has order dividing $6$, so $H K$ is not a subgroup. The lemma on products needs a normal factor.

**Counterexample (The correspondence needs $N \le K$).** In $\mathbb{Z}$ with $N = 6\mathbb{Z}$, the subgroups $4\mathbb{Z}$ and $2\mathbb{Z}$ have the same image $\langle 2 \rangle$ in $\mathbb{Z}/6$. So $K \mapsto K/N$ is not injective on all subgroups. Only the subgroups that contain $6\mathbb{Z}$ correspond to subgroups of $\mathbb{Z}/6$.

### The library around it

The isomorphism theorems are all in `Mathlib.GroupTheory.QuotientGroup.Basic`, with variants: `QuotientGroup.quotientMulEquivOfEq` for equal subgroups, `QuotientGroup.quotientBot` for $G/\{1\} \cong G$, and `QuotientGroup.congr` for a quotient by an isomorphic pair. The additive copies are `QuotientAddGroup.quotientInfEquivSumNormalQuotient` and `QuotientAddGroup.quotientQuotientEquivQuotient`. The same theorems for modules, rings and other structures are in their own volumes.

Common errors of a learner:

- In Mathlib the subgroup $M/N$ is `M.map (QuotientGroup.mk' N)`, not a quotient of `↥M`. The second theorem uses `subgroupOf` instead. The two forms are different types.
- The second theorem needs only $N$ normal. The subgroup $H$ can be any subgroup.
- A statement about indices should use `Subgroup.index` and `Subgroup.relIndex`, which have lemmas for these quotients, rather than cardinalities of quotient types.

### Exercises

1. (A) Use the third theorem to show that $(\mathbb{Z}/24)/(6\mathbb{Z}/24\mathbb{Z}) \cong \mathbb{Z}/6$.
2. (A) List the subgroups of $\mathbb{Z}/18$ that contain $\langle 6 \rangle$, by the correspondence theorem.
3. (B) Show that $|H K| = |H| \, |K| / |H \cap K|$ for any two finite subgroups. Hint: the map $H \times K \to H K$ has fibres of size $|H \cap K|$.
4. (B) Let $N \trianglelefteq G$ with $[G : N] = p$ prime. Show that there is no subgroup strictly between $N$ and $G$.
5. (B) Show that $\mathrm{GL}_2(\mathbb{R})$ has a normal subgroup $K$ with $\mathrm{SL}_2(\mathbb{R}) \le K$ and $\mathrm{GL}_2(\mathbb{R})/K \cong \mathbb{Z}/2$. Hint: use the sign of the determinant.
6. (C) Let $M, N \trianglelefteq G$ with $M N = G$. Show that $G/(M \cap N) \cong G/M \times G/N$. Hint: map $g$ to $(g M, g N)$.

### Notes and history

Emmy Noether stated the three isomorphism theorems in 1927, for modules over a ring, in "Abstrakter Aufbau der Idealtheorie in algebraischen Zahl- und Funktionenkörpern". The group cases were known earlier in pieces, in the work of Jordan and of Hölder on composition series. Hölder used the third theorem in 1889 to prove that the factors of a composition series are unique up to order, the Jordan-Hölder theorem. The numbering of the theorems varies between books, and some books call the correspondence theorem the fourth isomorphism theorem.

In Mathlib, the correspondence theorem is an order isomorphism, so the facts that it keeps meets and joins come for free from the order theory of Volume 4.

### Reference

<?reference?>
