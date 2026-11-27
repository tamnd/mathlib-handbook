---
title: Functoriality and exactness
kind: theory
modules:
  - Mathlib.LinearAlgebra.TensorProduct.Map
  - Mathlib.LinearAlgebra.TensorProduct.Associator
  - Mathlib.LinearAlgebra.TensorProduct.RightExactness
  - Mathlib.LinearAlgebra.TensorProduct.Quotient
  - Mathlib.LinearAlgebra.TensorProduct.Prod
  - Mathlib.LinearAlgebra.TensorProduct.Pi
  - Mathlib.LinearAlgebra.DirectSum.TensorProduct
explains:
  E3: [TensorProduct.map, rTensor_exact, TensorProduct.quotTensorEquivQuotSMul]
  E2: [TensorProduct.map_tmul, TensorProduct.map_comp, LinearMap.lTensor, LinearMap.rTensor, TensorProduct.congr, TensorProduct.assoc, TensorProduct.lid, TensorProduct.rid, TensorProduct.prodRight, TensorProduct.piRight, TensorProduct.directSum, lTensor_exact, LinearMap.rTensor_surjective, TensorProduct.tensorQuotEquivQuotSMul]
  E1: auto
families: []
requires: [V08.C01, V07.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Functoriality and exactness

### Overview

This section uses Section 1 of this chapter. A pair of linear maps $f : M \to M'$ and $g : N \to N'$ gives a linear map $f \otimes g$. The tensor product is associative and has $R$ as a unit, up to canonical isomorphisms, and it commutes with direct sums. The main theorem says that the tensor product is right exact: it keeps the exactness of $M' \to M \to M'' \to 0$. From this follows $(R / I) \otimes_R M \cong M / I M$. The tensor product is not left exact.

### Definitions

Fix a commutative ring $R$. All tensor products are over $R$.

**Definition (Tensor product of maps).** Let $f : M \to M'$ and $g : N \to N'$ be linear. The map $(m, n) \mapsto f(m) \otimes g(n)$ is bilinear, so by the universal property there is exactly one linear map
$$f \otimes g : M \otimes N \to M' \otimes N', \qquad (f \otimes g)(m \otimes n) = f(m) \otimes g(n).$$
Write $Q \otimes g$ for $\mathrm{id}_Q \otimes g$ and $f \otimes Q$ for $f \otimes \mathrm{id}_Q$.

**Proposition (Functoriality).** $\mathrm{id}_M \otimes \mathrm{id}_N = \mathrm{id}$, and $(f' \circ f) \otimes (g' \circ g) = (f' \otimes g') \circ (f \otimes g)$. The map $g \mapsto Q \otimes g$ is linear. If $f$ and $g$ are isomorphisms, so is $f \otimes g$.

*Proof.* In each identity both sides are linear and agree on the pure tensors: for example both sides of the second send $m \otimes n$ to $f'(f(m)) \otimes g'(g(n))$. Pure tensors generate (Section 1), so the two sides are equal. For linearity, $Q \otimes (g + h)$ and $Q \otimes g + Q \otimes h$ both send $q \otimes n$ to $q \otimes g(n) + q \otimes h(n)$. If $f$ and $g$ have inverses, then $f^{-1} \otimes g^{-1}$ is an inverse of $f \otimes g$ by the second identity. $\square$

::: mathlib
`TensorProduct.map` · `Mathlib.LinearAlgebra.TensorProduct.Map`

The map `TensorProduct.map f g : M ⊗[R] N →ₗ[R] M' ⊗[R] N'`, with `TensorProduct.map_tmul` for its value on pure tensors and `TensorProduct.map_comp` for the composition. The one-sided forms are `LinearMap.lTensor Q g : Q ⊗ N → Q ⊗ N'` and `LinearMap.rTensor Q f : M ⊗ Q → M' ⊗ Q`; the letter says on which side the module `Q` stands. For linear equivalences it is `TensorProduct.congr`.

<?decl TensorProduct.map?>
:::

### Theorems and proofs

**Theorem (Associativity and unit).** There are unique linear isomorphisms
$$(M \otimes N) \otimes P \cong M \otimes (N \otimes P), \quad (m \otimes n) \otimes p \mapsto m \otimes (n \otimes p), \qquad R \otimes M \cong M, \quad c \otimes m \mapsto c m.$$

*Proof.* Associativity. For a fixed $p$, the map $(m, n) \mapsto m \otimes (n \otimes p)$ is bilinear, so it gives a linear map $\varphi_p : M \otimes N \to M \otimes (N \otimes P)$. The map $p \mapsto \varphi_p$ is linear, by a check on pure tensors. So $(x, p) \mapsto \varphi_p(x)$ is bilinear and gives a linear $\alpha$ with $\alpha((m \otimes n) \otimes p) = m \otimes (n \otimes p)$. The same construction gives $\alpha'$ in the other direction. The elements $(m \otimes n) \otimes p$ generate $(M \otimes N) \otimes P$: each element is a sum of $x \otimes p$, and each $x$ is a sum of pure tensors, so $x \otimes p$ is a sum of $(m \otimes n) \otimes p$. The map $\alpha' \circ \alpha$ fixes these generators, so it is the identity; in the same way $\alpha \circ \alpha' = \mathrm{id}$. Uniqueness holds because the elements named generate.

Unit. The scalar multiplication $(c, m) \mapsto c m$ is bilinear, so it gives $\lambda : R \otimes M \to M$. Let $\mu(m) = 1 \otimes m$, a linear map. Then $\lambda(\mu(m)) = m$, and $\mu(\lambda(c \otimes m)) = 1 \otimes c m = c \otimes m$. So $\mu \circ \lambda$ fixes the pure tensors and is the identity. $\square$

::: mathlib
`TensorProduct.assoc` · `Mathlib.LinearAlgebra.TensorProduct.Associator`

The linear equivalence `TensorProduct.assoc R M N P : (M ⊗[R] N) ⊗[R] P ≃ₗ[R] M ⊗[R] (N ⊗[R] P)`. The units are `TensorProduct.lid R M : R ⊗[R] M ≃ₗ[R] M` and `TensorProduct.rid R M : M ⊗[R] R ≃ₗ[R] M`. A proof that moves brackets must apply `assoc` explicitly.

<?decl TensorProduct.assoc?>
<?decl TensorProduct.lid?>
:::

**Theorem (Direct sums).** There is an isomorphism $M \otimes (N_1 \oplus N_2) \cong (M \otimes N_1) \oplus (M \otimes N_2)$ with $m \otimes (n_1, n_2) \mapsto (m \otimes n_1, m \otimes n_2)$. In particular $M \otimes R^k \cong M^k$.

*Proof.* Let $\iota_j : N_j \to N_1 \oplus N_2$ and $\pi_j : N_1 \oplus N_2 \to N_j$ be the inclusions and projections, so $\pi_j \iota_k$ is $\mathrm{id}$ for $j = k$ and $0$ otherwise, and $\iota_1 \pi_1 + \iota_2 \pi_2 = \mathrm{id}$. Put $\Phi = (M \otimes \pi_1, M \otimes \pi_2)$ and $\Psi(x_1, x_2) = (M \otimes \iota_1)(x_1) + (M \otimes \iota_2)(x_2)$. By functoriality and the linearity of $g \mapsto M \otimes g$,
$$\Psi \circ \Phi = M \otimes (\iota_1 \pi_1 + \iota_2 \pi_2) = \mathrm{id}, \qquad (M \otimes \pi_j) \circ (M \otimes \iota_k) = M \otimes (\pi_j \iota_k).$$
The second identity gives $\Phi \circ \Psi = \mathrm{id}$. For $R^k$, use induction on $k$ and $M \otimes R \cong M$. $\square$

::: mathlib
`TensorProduct.directSum` · `Mathlib.LinearAlgebra.DirectSum.TensorProduct`

The isomorphism `(⨁ i₁, M₁ i₁) ⊗[R] (⨁ i₂, M₂ i₂) ≃ₗ (⨁ i : ι₁ × ι₂, M₁ i.1 ⊗[R] M₂ i.2)` for direct sums over arbitrary index types. The finite forms are `TensorProduct.prodRight` for a product of two modules and `TensorProduct.piRight` for a finite product `∀ i, M i`.

<?decl TensorProduct.directSum?>
<?decl TensorProduct.prodRight?>
:::

**Theorem (Right exactness).** Let $M' \xrightarrow{f} M \xrightarrow{g} M'' \to 0$ be exact, so $g$ is surjective and $\ker g = \operatorname{im} f$. For each module $Q$ the sequence
$$M' \otimes Q \xrightarrow{f \otimes Q} M \otimes Q \xrightarrow{g \otimes Q} M'' \otimes Q \to 0$$
is exact.

*Proof.* Surjectivity. Each pure tensor $m'' \otimes q$ equals $(g \otimes Q)(m \otimes q)$ for an $m$ with $g(m) = m''$. The image of $g \otimes Q$ is a submodule that contains a generating set, so it is everything.

The composition. $(g \otimes Q) \circ (f \otimes Q) = (g f) \otimes Q = 0$, so $E = \operatorname{im}(f \otimes Q)$ lies in $\ker(g \otimes Q)$.

The kernel. The map $g \otimes Q$ vanishes on $E$, so it induces a linear map $\bar g : (M \otimes Q) / E \to M'' \otimes Q$. It suffices to show that $\bar g$ is injective, and for this an inverse is built. Define $\beta : M'' \times Q \to (M \otimes Q) / E$ by $\beta(m'', q) = [m \otimes q]$, where $m$ is any element with $g(m) = m''$. This does not depend on the choice: if $g(m) = g(m_1)$, then $m - m_1 \in \ker g = \operatorname{im} f$, say $m - m_1 = f(m')$, and $(m - m_1) \otimes q = (f \otimes Q)(m' \otimes q) \in E$. The map $\beta$ is bilinear: if $m_1, m_2$ lift $m_1'', m_2''$, then $m_1 + m_2$ lifts $m_1'' + m_2''$ and $c m_1$ lifts $c m_1''$, and the rules of $\otimes$ give the four identities. Let $\bar\beta : M'' \otimes Q \to (M \otimes Q) / E$ be the induced linear map. For a pure tensor, $\bar\beta(\bar g([m \otimes q])) = \beta(g(m), q) = [m \otimes q]$. The classes $[m \otimes q]$ generate the quotient, so $\bar\beta \circ \bar g = \mathrm{id}$, and $\bar g$ is injective. Hence $\ker(g \otimes Q) = E$. $\square$

By the symmetry $M \otimes Q \cong Q \otimes M$ of Section 1, the same holds with $Q$ on the left.

::: mathlib
`rTensor_exact` · `Mathlib.LinearAlgebra.TensorProduct.RightExactness`

The statement `Function.Exact (rTensor Q f) (rTensor Q g)` from the hypotheses `Function.Exact f g` and `Function.Surjective g`, over a commutative ring. The left form is `lTensor_exact`, and the surjectivity is `LinearMap.rTensor_surjective`. The Mathlib proof builds the inverse as above.

<?decl rTensor_exact?>
<?decl lTensor_exact?>
:::

**Corollary (Quotients of the ring).** For an ideal $I$ of $R$ and a module $M$, there is an isomorphism $(R / I) \otimes M \cong M / I M$ with $\bar c \otimes m \mapsto [c m]$.

*Proof.* The sequence $I \to R \to R / I \to 0$ is exact. Tensor it with $M$ on the right and use $R \otimes M \cong M$, $c \otimes m \mapsto c m$:
$$I \otimes M \to M \to (R / I) \otimes M \to 0.$$
The image of $I \otimes M$ in $M$ is spanned by the elements $a m$ with $a \in I$, so it is $I M$. By right exactness, $(R / I) \otimes M$ is the cokernel $M / I M$. $\square$

::: mathlib
`TensorProduct.quotTensorEquivQuotSMul` · `Mathlib.LinearAlgebra.TensorProduct.Quotient`

The equivalence `((R ⧸ I) ⊗[R] M) ≃ₗ[R] M ⧸ (I • ⊤)`, where `I • ⊤` is the submodule $I M$. The version with $R / I$ on the right is `TensorProduct.tensorQuotEquivQuotSMul`.

<?decl TensorProduct.quotTensorEquivQuotSMul?>
:::

### Examples

**Example ($\mathbb{Z}/m \otimes \mathbb{Z}/n$ again).** Take $R = \mathbb{Z}$, $I = m \mathbb{Z}$ and $M = \mathbb{Z}/n$. Then $I M = m (\mathbb{Z}/n)$ is the subgroup generated by $\bar m$, which is the subgroup generated by $\bar d$ for $d = \gcd(m, n)$, since $d = u m + v n$. So $\mathbb{Z}/m \otimes \mathbb{Z}/n \cong (\mathbb{Z}/n) / (d \mathbb{Z}/n \mathbb{Z}) \cong \mathbb{Z}/d$. For $m = 6$, $n = 4$: the multiples of $6$ in $\mathbb{Z}/4$ are $\{0, 2\}$, and the quotient is $\mathbb{Z}/2$.

**Example (A presentation).** Let $M$ be the cokernel of the map $\mathbb{Z}^2 \to \mathbb{Z}^2$ with the matrix $A = \begin{pmatrix} 2 & 0 \\ 0 & 3 \end{pmatrix}$, so $M \cong \mathbb{Z}/2 \oplus \mathbb{Z}/3$. Tensor with $\mathbb{Z}/3$. By right exactness and $\mathbb{Z}^2 \otimes \mathbb{Z}/3 \cong (\mathbb{Z}/3)^2$, the module $M \otimes \mathbb{Z}/3$ is the cokernel of $A$ read modulo $3$, that is $\operatorname{diag}(2, 0)$ on $(\mathbb{Z}/3)^2$. Since $2$ is a unit modulo $3$, only the second coordinate survives. So $M \otimes \mathbb{Z}/3 \cong \mathbb{Z}/3$.

**Counterexample (The tensor product is not left exact).** The map $f : \mathbb{Z} \to \mathbb{Z}$, $x \mapsto 2 x$, is injective. Tensor with $\mathbb{Z}/2$ and identify $\mathbb{Z} \otimes \mathbb{Z}/2 \cong \mathbb{Z}/2$ by the unit isomorphism. The map $f \otimes \mathbb{Z}/2$ becomes $\bar a \mapsto 2 \bar a = 0$ on $\mathbb{Z}/2$. It is zero, so it is not injective.

### The library around it

A module $Q$ for which $Q \otimes -$ keeps all injective maps is flat, the class `Module.Flat` of `Mathlib.RingTheory.Flat.Basic`. Free modules are flat, and $\mathbb{Z}/2$ is not flat over $\mathbb{Z}$ by the counterexample.

### Exercises

1. (A) Show that $(f \otimes g) = (f \otimes N') \circ (M \otimes g)$. Hint: functoriality.
2. (A) Compute $\mathbb{Z}/12 \otimes \mathbb{Z}/18$ with the corollary on quotients. Hint: $\gcd(12, 18) = 6$.
3. (A) Show that $R^m \otimes R^n \cong R^{m n}$. Hint: the theorem on direct sums, twice.
4. (B) Show that $(R / I) \otimes (R / J) \cong R / (I + J)$. Hint: apply the corollary to $M = R / J$; then $I M = (I + J) / J$.
5. (B) Let $M = \mathbb{Z}^2 / \operatorname{im}(A)$ for $A = \begin{pmatrix} 4 & 2 \\ 0 & 6 \end{pmatrix}$. Compute $M \otimes \mathbb{Z}/2$. Hint: $A$ modulo $2$ is $0$.
6. (B) Show that $\mathbb{Q} \otimes_{\mathbb{Z}} -$ keeps the injectivity of $x \mapsto 2 x$ on $\mathbb{Z}$. Hint: $\mathbb{Q} \otimes \mathbb{Z} \cong \mathbb{Q}$, and $2$ is invertible in $\mathbb{Q}$.
7. (C) Show that $M \otimes \bigoplus_{i} N_i \cong \bigoplus_i (M \otimes N_i)$ for an arbitrary family. Hint: build the inverse from the inclusions of the summands.

### Notes and history

Right exactness and the failure of left exactness are the starting point of homological algebra, where the groups $\operatorname{Tor}_n$ measure the failure; Cartan and Eilenberg made this systematic in their book of 1956.

### Reference

<?reference?>
