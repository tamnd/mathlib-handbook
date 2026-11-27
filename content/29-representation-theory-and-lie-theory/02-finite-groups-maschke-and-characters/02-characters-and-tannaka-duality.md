---
title: Characters and Tannaka duality
kind: theory
modules:
  - Mathlib.RepresentationTheory.Character
  - Mathlib.RepresentationTheory.Tannaka
explains:
  E3: [Representation.character, Representation.char_conj, Representation.char_tensor, Representation.char_dual, Representation.char_linHom, Representation.card_inv_mul_sum_char_eq_finrank, Representation.card_inv_mul_sum_char_mul_char_eq_finrank, Representation.char_orthonormal, FDRep.character, FDRep.char_orthonormal, FDRep.scalar_product_char_eq_finrank_equivariant, TannakaDuality.FiniteGroup.equiv]
  E2: [Representation.char_one, Representation.char_mul_comm, Representation.char_iso, Representation.isIntegral_character, FDRep.char_one, FDRep.char_tensor, FDRep.char_iso, FDRep.char_dual, FDRep.char_linHom, FDRep.char_conj, FDRep.average_char_eq_finrank_invariants, FDRep.isIntegral_character, TannakaDuality.FiniteGroup.forget, TannakaDuality.FiniteGroup.equivHom, TannakaDuality.FiniteGroup.equivApp, TannakaDuality.FiniteGroup.rightRegular, TannakaDuality.FiniteGroup.leftRegular, TannakaDuality.FiniteGroup.rightFDRep, TannakaDuality.FiniteGroup.equivHom_injective, TannakaDuality.FiniteGroup.equivHom_surjective, TannakaDuality.FiniteGroup.algHomOfRightFDRepComp, TannakaDuality.FiniteGroup.ofRightFDRep, TannakaDuality.FiniteGroup.toRightFDRepComp_in_rightRegular, TannakaDuality.FiniteGroup.mulRepHom, TannakaDuality.FiniteGroup.sumSMulInv, TannakaDuality.FiniteGroup.leftRegularFDRepHom, TannakaDuality.FiniteGroup.toRightFDRepComp_injective]
  E1: auto
families: []
requires: [V29.C01, V07.C03, V07.C05, V08.C02, V24.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Characters and Tannaka duality

### Overview

A finite dimensional representation is a list of matrices, one for each group element, and the matrices change by conjugation when the basis changes. The trace is the simplest number that survives this change. The character of a representation is the function $g \mapsto \operatorname{tr} \rho(g)$, and for finite groups over an algebraically closed field of characteristic zero it carries much information: the average of a character is the dimension of the invariants, the inner product of two characters is the dimension of the space of intertwining maps, and the characters of the irreducible representations are orthonormal.

The second half of the section asks the reverse question: how much of the group the representations remember. Tannaka duality answers that the whole group comes back from the monoidal category $\mathbf{FDRep}_k(G)$ together with the forgetful functor to vector spaces: $G$ is the group of monoidal natural automorphisms of that functor. Characters alone do not suffice, since the dihedral and quaternion groups of order $8$ have the same character table.

In this section $k$ is a field and $G$ a group, except in the Tannaka theorem, where $k$ is a commutative domain and $G$ is finite. All representations are finite dimensional.

### Definitions

**Definition (Character).** The character of a representation $\rho$ of $G$ on $V$ is the function $\chi_\rho \colon G \to k$, $\chi_\rho(g) = \operatorname{tr} \rho(g)$.

**Definition (Inner product of functions).** For a finite group $G$ of order $n$ invertible in $k$ and functions $\phi, \psi \colon G \to k$, put
$$\langle \phi, \psi \rangle = \frac{1}{n} \sum_{g \in G} \phi(g)\, \psi(g^{-1}).$$
Over $\mathbb{C}$ with $\psi$ a character, $\psi(g^{-1}) = \overline{\psi(g)}$, and this is the usual Hermitian product; Mathlib uses the form with $g^{-1}$, which makes sense over each field.

**Definition (Automorphisms of the forgetful functor).** Let $\mathrm{forget} \colon \mathbf{FDRep}_k(G) \to \mathrm{FGMod}_k$ be the monoidal forgetful functor. A monoidal natural automorphism $\eta$ of it is a family of $k$-linear automorphisms $\eta_X \colon X \to X$, one for each representation $X$, such that $\phi \circ \eta_X = \eta_Y \circ \phi$ for each morphism $\phi \colon X \to Y$, $\eta_{X \otimes Y} = \eta_X \otimes \eta_Y$, and $\eta_k = \mathrm{id}$ on the unit. They form a group $\mathrm{Aut}(\mathrm{forget})$ under composition.

**Definition (The regular representations on functions).** On $k^G$, the space of functions $G \to k$, the right regular representation is $(R_s f)(t) = f(ts)$ and the left regular representation is $(L_s f)(t) = f(s^{-1} t)$. Write $\delta_t$ for the function that is $1$ at $t$ and $0$ elsewhere.

### Theorems and proofs

**Proposition (First properties).** Let $\rho$, $\sigma$ be representations on $V$, $W$.

1. $\chi_\rho(1) = \dim V$ and $\chi_\rho(hgh^{-1}) = \chi_\rho(g)$.
2. Equivalent representations have the same character.
3. $\chi_{\rho \otimes \sigma} = \chi_\rho \chi_\sigma$, $\chi_{\rho^*}(g) = \chi_\rho(g^{-1})$ and $\chi_{\mathrm{Hom}(\rho, \sigma)}(g) = \chi_\rho(g^{-1})\chi_\sigma(g)$.
4. If $G$ is finite, each $\chi_\rho(g)$ is integral over $\mathbb{Z}$.

*Proof.* (1) $\rho(1) = \mathrm{id}_V$ has trace $\dim V$. By $\operatorname{tr}(AB) = \operatorname{tr}(BA)$ (Volume 7, Chapter 3), $\chi(hgh^{-1}) = \operatorname{tr}(\rho(h)\rho(g h^{-1})) = \operatorname{tr}(\rho(gh^{-1})\rho(h)) = \chi(g)$. (2) If $\phi$ is an equivalence, $\sigma(g) = \phi \rho(g) \phi^{-1}$, and the trace is invariant under conjugation. (3) The trace of $A \otimes B$ is $\operatorname{tr} A \cdot \operatorname{tr} B$: in the basis $v_i \otimes w_j$ the diagonal entries are $a_{ii} b_{jj}$. The dual acts by the transpose of $\rho(g^{-1})$, with the same trace. For $\mathrm{Hom}$, use the equivalence $V^* \otimes W \cong \mathrm{Hom}(V, W)$ of Chapter 1 with (2) and the first two formulas. (4) Let $n = |G|$. Over an algebraic closure $\bar k$, $\chi(g)$ is the sum of the eigenvalues of $\rho(g)$ with multiplicity. Since $\rho(g)^n = \rho(g^n) = \mathrm{id}$, each eigenvalue $\lambda$ satisfies $\lambda^n = 1$, so it is integral over $\mathbb{Z}$; a sum of integral elements is integral. $\square$

**Theorem (Average of a character).** Let $G$ be finite with order $n$ invertible in $k$. Then $\frac{1}{n}\sum_g \chi_\rho(g) = \dim V^G$ in $k$.

*Proof.* The averaging map $P = \frac{1}{n}\sum_g \rho(g)$ is a projection onto $V^G$ (Chapter 1). Choose a basis of $V^G$ and a basis of $\ker P$; together they form a basis of $V$, in which $P$ is diagonal with $\dim V^G$ entries $1$ and the rest $0$. So $\operatorname{tr} P = \dim V^G$. The trace is linear, so $\operatorname{tr} P = \frac{1}{n}\sum_g \chi_\rho(g)$. $\square$

**Theorem (Inner product and intertwining maps).** Under the same hypothesis, $\langle \chi_\sigma, \chi_\rho \rangle = \dim \mathrm{Hom}_G(V, W)$, that is,
$$\frac{1}{n}\sum_{g} \chi_\sigma(g)\, \chi_\rho(g^{-1}) = \dim_k \mathrm{Hom}_G(\rho, \sigma).$$

*Proof.* Apply the previous theorem to the representation $\mathrm{Hom}(\rho, \sigma)$, whose character is $\chi_\rho(g^{-1})\chi_\sigma(g)$ by the proposition. Its invariants are $\mathrm{Hom}_G(\rho, \sigma)$ by Chapter 1. $\square$

**Corollary (Orthonormality).** Let $k$ be algebraically closed, $G$ finite with order invertible in $k$, and $\rho$, $\sigma$ irreducible. Then $\langle \chi_\rho, \chi_\sigma \rangle$ is $1$ if $\rho$ and $\sigma$ are equivalent and $0$ otherwise.

*Proof.* By the theorem, $\langle \chi_\rho, \chi_\sigma \rangle = \dim \mathrm{Hom}_G(\sigma, \rho)$. By the lemma of Schur (Section 1), this dimension is $1$ if $\sigma \cong \rho$ and $0$ otherwise. $\square$

**Corollary (Multiplicities).** In the setting of the last corollary, assume $\mathrm{char}\, k = 0$. If $V \cong \bigoplus_i V_i^{m_i}$ with the $V_i$ irreducible and pairwise not equivalent, then $m_i = \langle \chi_V, \chi_{V_i} \rangle$. Hence two representations with the same character are equivalent, and $V$ is irreducible if and only if $\langle \chi_V, \chi_V \rangle = 1$.

*Proof.* The character of a direct sum is the sum of the characters, since the matrix of $\rho(g)$ is block diagonal. So $\chi_V = \sum_i m_i \chi_{V_i}$, and bilinearity with orthonormality gives $\langle \chi_V, \chi_{V_i} \rangle = m_i$ as an element of $k$; in characteristic $0$ this determines the integer $m_i$. By Maschke, each $V$ has such a decomposition, so the character fixes all multiplicities, and $V$ up to equivalence. Finally $\langle \chi_V, \chi_V \rangle = \sum_i m_i^2$, which is $1$ exactly when one $m_i$ is $1$ and the rest are $0$. $\square$

The index of this edition has no declaration for the statement that two representations with the same character are equivalent, nor for the statement that the number of irreducible representations equals the number of conjugacy classes. The last claim of the corollary is `FDRep.simple_iff_char_is_norm_one` in `Mathlib.RepresentationTheory.FinGroupCharZero`.

**Theorem (Tannaka duality for finite groups).** Let $k$ be a commutative domain and $G$ a finite group. The map $G \to \mathrm{Aut}(\mathrm{forget})$, $g \mapsto (\rho_X(g))_X$, is an isomorphism of groups.

*Proof.* Write $\Phi(g)$ for the family $(\rho_X(g))_X$. It is natural, because each morphism $\phi$ intertwines: $\phi \circ \rho_X(g) = \rho_Y(g) \circ \phi$. It is monoidal, because $g$ acts on $X \otimes Y$ by $\rho_X(g) \otimes \rho_Y(g)$ and on the unit trivially. Each $\Phi(g)$ is invertible with inverse $\Phi(g^{-1})$, and $\Phi(gh) = \Phi(g)\Phi(h)$, so $\Phi$ is a group homomorphism. Let $R$ be $k^G$ with the right regular representation; then $R_s \delta_t = \delta_{ts^{-1}}$, since $\delta_t(us) = 1$ exactly when $u = ts^{-1}$.

Injectivity. If $\Phi(s) = \Phi(t)$, the components on $R$ agree at $\delta_1$, so $\delta_{s^{-1}} = \delta_{t^{-1}}$. As $1 \ne 0$ in the domain $k$, this forces $s = t$.

Step 1: the component on $R$ is an algebra map. Let $\eta \in \mathrm{Aut}(\mathrm{forget})$ and $\alpha = \eta_R$. The pointwise product $m \colon R \otimes R \to R$, $f \otimes f' \mapsto f f'$, is a morphism, because $R_s(ff') = R_s(f) R_s(f')$. Naturality for $m$ and the rule $\eta_{R \otimes R} = \alpha \otimes \alpha$ give $\alpha(ff') = \alpha(f)\alpha(f')$. Since $\alpha$ is bijective, choose $f$ with $\alpha(f) = 1$; then $\alpha(1) = \alpha(1)\alpha(f) = \alpha(f) = 1$. So $\alpha$ is a $k$-algebra endomorphism of $k^G$.

Step 2: evaluation. The map $\varphi = \mathrm{ev}_1 \circ \alpha \colon k^G \to k$ is a $k$-algebra map. The functions $\delta_t$ are idempotents with $\delta_t \delta_u = 0$ for $t \ne u$ and $\sum_t \delta_t = 1$. Each $\varphi(\delta_t)$ is an idempotent of the domain $k$, so it is $0$ or $1$; the values sum to $1$, and two of them cannot both be $1$, because their product is $\varphi(0) = 0$. So there is exactly one $s \in G$ with $\varphi(\delta_s) = 1$, and $\varphi(f) = \sum_t f(t)\varphi(\delta_t) = f(s)$.

Step 3: $\alpha = R_s$. Each $L_t$ is an endomorphism of the representation $R$, since left and right translations commute. Naturality gives $\alpha \circ L_t = L_t \circ \alpha$. Then for $f \in k^G$ and $t \in G$,
$$\alpha(f)(t) = (L_{t^{-1}}\alpha(f))(1) = \alpha(L_{t^{-1}} f)(1) = (L_{t^{-1}} f)(s) = f(ts) = (R_s f)(t).$$

Step 4: the component on $R$ determines $\eta$. For a representation $X$ and $v \in X$, the linear map $\psi_v \colon R \to X$, $f \mapsto \sum_u f(u)\, \rho_X(u^{-1}) v$, is a morphism: with $w = ut$,
$$\psi_v(R_t f) = \sum_u f(ut)\, \rho_X(u^{-1}) v = \sum_w f(w)\, \rho_X(t w^{-1}) v = \rho_X(t)\psi_v(f).$$
Also $\psi_v(\delta_1) = v$. Naturality gives $\eta_X(v) = \eta_X(\psi_v(\delta_1)) = \psi_v(\eta_R(\delta_1))$. The same holds for $\Phi(s)$, and $\eta_R = R_s = \Phi(s)_R$ by Step 3. So $\eta_X = \Phi(s)_X$ for each $X$, and $\eta = \Phi(s)$. $\square$

### Examples

**Example (The character table of $S_3$).** Over $\mathbb{C}$ the group $S_3$ has the three classes $\{e\}$, the three transpositions and the two $3$-cycles. The irreducible representations of Section 1 have the characters below; for $W$, a transposition has eigenvalues $1, -1$ and a $3$-cycle has eigenvalues $\zeta_3, \zeta_3^2$.

| | $e$ (1) | $(1\,2)$ (3) | $(1\,2\,3)$ (2) |
|---|---|---|---|
| trivial | $1$ | $1$ | $1$ |
| sign | $1$ | $-1$ | $1$ |
| $W$ | $2$ | $0$ | $-1$ |

Each element is conjugate to its inverse in $S_3$, so $\chi(g^{-1}) = \chi(g)$ and the inner product sums over classes with weights $1, 3, 2$. Then $\langle \chi_W, \chi_W \rangle = \frac{1}{6}(4 + 0 + 2) = 1$, $\langle \chi_W, 1 \rangle = \frac{1}{6}(2 + 0 - 2) = 0$, $\langle \chi_W, \operatorname{sgn} \rangle = 0$ and $\langle 1, \operatorname{sgn} \rangle = \frac{1}{6}(1 - 3 + 2) = 0$, as orthonormality predicts.

**Example (Decompositions by characters).** The permutation representation on $\mathbb{C}^3$ has character $(3, 1, 0)$, the number of fixed points, and $(3, 1, 0) = (1, 1, 1) + (2, 0, -1)$, so it is $1 \oplus W$. The tensor square $W \otimes W$ has character $\chi_W^2 = (4, 0, 1)$, and $(4, 0, 1) = 1 + \operatorname{sgn} + \chi_W$, so $W \otimes W \cong 1 \oplus \operatorname{sgn} \oplus W$.

**Example (Cyclic groups).** Over $\mathbb{C}$ the irreducible representations of $\mathbb{Z}/n$ are the characters $\chi_j(m) = \zeta^{jm}$ with $\zeta = e^{2\pi i/n}$ and $0 \le j < n$. Orthonormality reads $\frac{1}{n}\sum_m \zeta^{(j - l)m} = 1$ if $j = l$ and $0$ otherwise, the familiar sum of a geometric series of roots of unity.

**Counterexample (Characters in positive characteristic).** Over $\mathbb{F}_p$, the trivial representation of dimension $p$ has character $p = 0$ at each $g$, the same as the zero representation. So characters do not determine representations without the hypothesis $\mathrm{char}\, k = 0$.

**Remark (Characters do not determine the group).** The dihedral group $D_4$ and the quaternion group $Q_8$ of order $8$ have the same character table: five classes, four characters of degree $1$ and one of degree $2$, with equal values. The groups are not isomorphic, so the table alone does not recover the group. Tannaka duality uses more: the tensor product of representations and the forgetful functor. The two categories $\mathbf{FDRep}_{\mathbb{C}}(D_4)$ and $\mathbf{FDRep}_{\mathbb{C}}(Q_8)$ are not monoidally equivalent over the forgetful functors, since the theorem would then make the groups isomorphic.

### The library around it

::: mathlib
`Representation.character` · `Mathlib.RepresentationTheory.Character`

`ρ.character g = LinearMap.trace k V (ρ g)` for a monoid `G` and a field `k`. The monoid lemmas are `char_one`, `char_mul_comm`, `char_tensor` and `char_iso`; the group lemmas are `char_conj`, `char_dual`, `char_linHom` and `isIntegral_character`. Under `[Fintype G] [Invertible (Nat.card G : k)]`, `card_inv_mul_sum_char_eq_finrank` is the average theorem and `card_inv_mul_sum_char_mul_char_eq_finrank` the inner product theorem, with right side `finrank k (IntertwiningMap ρ σ)`. With `[IsAlgClosed k]` and both representations irreducible, `char_orthonormal` gives `if Nonempty (Equiv σ ρ) then 1 else 0`.

<?decl Representation.char_orthonormal?>
:::

::: mathlib
`FDRep.character` · `Mathlib.RepresentationTheory.Character`

The same theory for objects of `FDRep k G`: `FDRep.character V g` is the trace of `V.ρ g`, with `FDRep.char_one`, `FDRep.char_tensor`, `FDRep.char_iso` for an isomorphism in the category, `FDRep.char_dual`, `FDRep.char_linHom` and `FDRep.char_conj`. `average_char_eq_finrank_invariants` and `scalar_product_char_eq_finrank_equivariant`, with right side `Module.finrank k (V ⟶ W)`, are the two dimension theorems, and `FDRep.char_orthonormal` assumes `[Simple V] [Simple W]` and reads `if Nonempty (V ≅ W) then 1 else 0`.

<?decl FDRep.scalar_product_char_eq_finrank_equivariant?>
:::

::: mathlib
`TannakaDuality.FiniteGroup.equiv` · `Mathlib.RepresentationTheory.Tannaka`

`forget k G` is the forgetful functor `FDRep k G ⥤ FGModuleCat k` as a lax monoidal functor, and `equivApp g X` and `equivHom : G →* Aut (forget k G)` form the map $\Phi$. `rightRegular`, `leftRegular` and `rightFDRep` are the representations on `G → k`. The proof follows the four steps above: `equivHom_injective` needs `[Nontrivial k]`; `mulRepHom` and `algHomOfRightFDRepComp` are Step 1; `toRightFDRepComp_in_rightRegular` (with `[IsDomain k]`) and `leftRegularFDRepHom` are Steps 2 and 3; `sumSMulInv`, `ofRightFDRep` and `toRightFDRepComp_injective` are Step 4; `equivHom_surjective` and `equiv [IsDomain k] : G ≃* Aut (forget k G)` conclude, for `[Finite G]`.

<?decl TannakaDuality.FiniteGroup.equiv?>
:::

Common errors of a learner: The first error is to write the inner product with complex conjugation; Mathlib uses $\chi(g^{-1})$, and the order of the two characters in `card_inv_mul_sum_char_mul_char_eq_finrank` decides the direction of the intertwining maps. The second error is to expect `char_orthonormal` over $\mathbb{Q}$ or $\mathbb{R}$; it needs `IsAlgClosed k`. The third error is to treat `Representation.char_iso` and `FDRep.char_iso` as one lemma; the first takes a `Representation.Equiv` and the second an isomorphism in `FDRep k G`.

### Exercises

1. (A) Show that a one dimensional representation equals its own character, and that the character of the sign representation of $S_n$ is the sign.
2. (A) Show that the character of a permutation representation $k[X]$ at $g$ is the number of fixed points of $g$ on $X$.
3. (A) Use characters to show that the regular representation of $\mathbb{Z}/3$ over $\mathbb{C}$ is $\chi_0 \oplus \chi_1 \oplus \chi_2$. Hint: its character is $(3, 0, 0)$.
4. (B) Show that the regular representation $\mathbb{C}[G]$ of a finite group contains each irreducible $V$ with multiplicity $\dim V$. Hint: compute $\langle \chi_{\mathbb{C}[G]}, \chi_V \rangle$ with exercise 2.
5. (B) Compute the character of $\operatorname{sgn} \otimes W$ for $S_3$ and identify it. Hint: $(2, 0, -1)$ times $(1, -1, 1)$.
6. (C) In the proof of Tannaka duality, show that Step 2 fails for $k = \mathbb{Z}/6$ and $G = \mathbb{Z}/2$: find a $k$-algebra map $k^G \to k$ that is not an evaluation at a point. Hint: the idempotents of $\mathbb{Z}/6$ are $0, 1, 3, 4$, and $3 + 4 = 1$, $3 \cdot 4 = 0$.

### Notes and history

Frobenius introduced group characters of finite groups in 1896. Schur gave the proof through his lemma in 1905. Tannaka proved his duality theorem for compact groups in 1939; for the finite group case the Mathlib file cites the Leiden bachelor thesis of Commelin. Mathlib authors, read from the file headers: `RepresentationTheory.Character` by Antoine Labelle; `RepresentationTheory.Tannaka` by Yacine Benmeuraiem.

### Reference

<?reference?>
