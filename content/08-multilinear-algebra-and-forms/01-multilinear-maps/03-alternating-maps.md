---
title: Alternating maps and the determinant
kind: theory
modules:
  - Mathlib.LinearAlgebra.Alternating.Basic
  - Mathlib.LinearAlgebra.Alternating.Curry
  - Mathlib.LinearAlgebra.Alternating.DomCoprod
  - Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
explains:
  E3: [AlternatingMap, AlternatingMap.map_perm, MultilinearMap.alternatization]
  E2: [AlternatingMap.map_eq_zero_of_eq, AlternatingMap.map_swap, AlternatingMap.map_eq_zero_of_not_injective, AlternatingMap.map_linearDependent, MultilinearMap.alternatization_apply, AlternatingMap.coe_alternatization, AlternatingMap.domCoprod, Equiv.Perm.ModSumCongr, MultilinearMap.domCoprod_alternatization_eq, Module.Basis.ext_alternating, AlternatingMap.domDomCongr, AlternatingMap.curryLeft, AlternatingMap.alternatizeUncurryFin]
  E1: auto
families: []
requires: [V07.C02, V07.C04, V05.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Alternating maps and the determinant

### Overview

The determinant is multilinear in the columns and vanishes when two columns are equal (Volume 7, Chapter 4). This section studies such maps on any module: permutations, the alternatization and the product of two alternating forms. The main theorem says that on a free module of rank $n$ the alternating maps of $n$ arguments are the multiples of the determinant. It uses Section 2 of this chapter and the sign of a permutation from Volume 5, Chapter 7.

### Definitions

Fix a commutative ring $R$, modules $M$ and $N$, and a finite set $\iota$. A tuple is a function $v : \iota \to M$, and for a permutation $\sigma$ of $\iota$ the tuple $v \circ \sigma$ has $v_{\sigma(i)}$ at the place $i$.

**Definition (Alternating map).** A multilinear map $f : M^\iota \to N$ is alternating if $f(v) = 0$ for each tuple $v$ with $v_i = v_j$ for some $i \neq j$.

They form a submodule $\operatorname{Alt}^\iota_R(M; N)$, written $\operatorname{Alt}^k_R(M; N)$ for $\iota = \{1, \dots, k\}$.

::: mathlib
`AlternatingMap` · `Mathlib.LinearAlgebra.Alternating.Basic`

A structure that extends `(ι → M) →ₘₗ[R] N` by the condition of the definition, with the notation `M [⋀^ι]→ₗ[R] N`. The lemma `AlternatingMap.map_eq_zero_of_eq` gives the field, and `AlternatingMap.map_eq_zero_of_not_injective` restates it for a tuple that is not injective.

<?decl AlternatingMap?>
:::

### Theorems and proofs

**Proposition (Antisymmetry).** Let $f$ be alternating and $i \neq j$. Then $f(v \circ \tau) = -f(v)$ for the transposition $\tau = (i\,j)$.

*Proof.* Let $w$ have $v_i + v_j$ at both places $i$ and $j$ and $v_k$ elsewhere, so $f(w) = 0$. Expand $f(w)$ at the places $i$ and $j$. Of the four terms, the two with $v_i$ at both places or $v_j$ at both places are $0$. The other two are $f(v)$ and $f(v \circ \tau)$. So $0 = f(v) + f(v \circ \tau)$. $\square$

**Theorem (Permutations).** Let $f$ be alternating. For each permutation $\sigma$ of $\iota$ and each tuple $v$, $f(v \circ \sigma) = \operatorname{sign}(\sigma) f(v)$.

*Proof.* Write $\sigma$ as a product of $k$ transpositions, so $\operatorname{sign}(\sigma) = (-1)^k$, and induct on $k$. If $\sigma = \rho \tau$ with $\tau$ a transposition, then $v \circ \sigma = (v \circ \rho) \circ \tau$. Antisymmetry and the hypothesis on $\rho$ give $f(v \circ \sigma) = -f(v \circ \rho) = -\operatorname{sign}(\rho) f(v) = \operatorname{sign}(\sigma) f(v)$. $\square$

::: mathlib
`AlternatingMap.map_perm` · `Mathlib.LinearAlgebra.Alternating.Basic`

The rule `g (v ∘ σ) = Equiv.Perm.sign σ • g v`, proved by the induction above from `AlternatingMap.map_swap`: `g (v ∘ Equiv.swap i j) = -g v`.

<?decl AlternatingMap.map_perm?>
:::

**Theorem (Linearly dependent families).** Let $K$ be an integral domain, $M$ and $N$ modules over $K$, and $N$ torsion free. If $f$ is alternating and the family $v$ is linearly dependent, then $f(v) = 0$.

*Proof.* Take a relation $\sum_k c_k v_k = 0$ with some $c_i \neq 0$. Then $c_i v_i = -\sum_{k \neq i} c_k v_k$. By the rules at the place $i$,
$$c_i f(v) = f(v[i \mapsto c_i v_i]) = -\sum_{k \neq i} c_k f(v[i \mapsto v_k]).$$
In the tuple $v[i \mapsto v_k]$ the places $i$ and $k$ hold the same vector $v_k$, so each term is $0$. Thus $c_i f(v) = 0$ with $c_i \neq 0$, and $f(v) = 0$ because $N$ is torsion free. $\square$

In Mathlib this is `AlternatingMap.map_linearDependent`.

**Definition (Alternatization).** Let $\iota$ be finite and $m : M^\iota \to N$ multilinear. Its alternatization is
$$\operatorname{Alt}(m)(v) = \sum_{\sigma} \operatorname{sign}(\sigma) \, m(v \circ \sigma),$$
where $\sigma$ runs over the permutations of $\iota$.

**Theorem (The alternatization).** $\operatorname{Alt}(m)$ is alternating. If $f$ is alternating, then $\operatorname{Alt}(f) = n! \, f$ with $n = |\iota|$.

*Proof.* The sum is multilinear. Let $v_i = v_j$ with $i \neq j$ and let $\tau = (i\,j)$, so $v \circ \tau = v$. Left multiplication by $\tau$ is a bijection of the permutations with $\tau \sigma \neq \sigma$ and $\tau(\tau \sigma) = \sigma$, so the permutations fall into pairs $\{\sigma, \tau \sigma\}$. In a pair, $v \circ (\tau \sigma) = (v \circ \tau) \circ \sigma = v \circ \sigma$ and $\operatorname{sign}(\tau \sigma) = -\operatorname{sign}(\sigma)$. The two terms cancel, so $\operatorname{Alt}(m)(v) = 0$. For alternating $f$, the theorem on permutations gives $\operatorname{sign}(\sigma) f(v \circ \sigma) = \operatorname{sign}(\sigma)^2 f(v) = f(v)$, and the sum has $n!$ terms. $\square$

::: mathlib
`MultilinearMap.alternatization` · `Mathlib.LinearAlgebra.Alternating.Basic`

An additive map from `(ι → M) →ₘₗ[R] N'` to `M [⋀^ι]→ₗ[R] N'`, with `MultilinearMap.alternatization_apply` for the formula $\sum_\sigma \operatorname{sign}(\sigma) \, m(v \circ \sigma)$. The alternating version of `domDomCongr` of Section 2 is `AlternatingMap.domDomCongr`. The second half of the theorem is `AlternatingMap.coe_alternatization`, with the factor `(Fintype.card ι)!`.

<?decl MultilinearMap.alternatization?>
:::

### The product of alternating forms

Let $a$ be an alternating form of $k$ arguments and $b$ one of $l$ arguments, both with values in $R$. The places $1, \dots, k$ and $k + 1, \dots, k + l$ form two blocks, and $S_k \times S_l \subseteq S_{k+l}$ is the subgroup that keeps both blocks. For a permutation $\sigma$ of $\{1, \dots, k + l\}$ put
$$P_\sigma(v) = \operatorname{sign}(\sigma) \, a(v_{\sigma(1)}, \dots, v_{\sigma(k)}) \, b(v_{\sigma(k+1)}, \dots, v_{\sigma(k+l)}).$$

If $\rho = (\rho_1, \rho_2) \in S_k \times S_l$, then $P_{\sigma \rho} = P_\sigma$: the sign changes by $\operatorname{sign}(\rho_1) \operatorname{sign}(\rho_2)$, and by the theorem on permutations the two factors change by the same signs. So $P_\sigma$ depends only on the coset of $\sigma$.

**Definition (Product).** The product $a \wedge b$ is the sum of $P_\sigma$ over a set of representatives $\sigma$ of the cosets of $S_k \times S_l$ in $S_{k+l}$.

There are $\binom{k+l}{k}$ cosets. Each one contains exactly one shuffle, a permutation that is increasing on $\{1, \dots, k\}$ and on $\{k + 1, \dots, k + l\}$.

**Theorem (The product is alternating).** $a \wedge b$ is an alternating form of $k + l$ arguments, and $\operatorname{Alt}(a \cdot b) = k! \, l! \, (a \wedge b)$, where $(a \cdot b)(v) = a(v_1, \dots, v_k) \, b(v_{k+1}, \dots, v_{k+l})$.

*Proof.* Each $P_\sigma$ is multilinear, as a product of a multilinear form in some places and one in the other places. Let $v_i = v_j$ with $i \neq j$ and $\tau = (i\,j)$. Then $v \circ \tau \sigma = v \circ \sigma$ and $\operatorname{sign}(\tau \sigma) = -\operatorname{sign}(\sigma)$, so $P_{\tau \sigma}(v) = -P_\sigma(v)$. Left multiplication by $\tau$ permutes the cosets. The cosets $C$ with $\tau C \neq C$ fall into pairs whose terms cancel. If $\tau C = C$ for $C = \sigma (S_k \times S_l)$, then $\sigma^{-1} \tau \sigma$ lies in $S_k \times S_l$. This is the transposition of $\sigma^{-1}(i)$ and $\sigma^{-1}(j)$, so both places lie in the same block. Then $v \circ \sigma$ has equal entries at two places of one block, and the factor $a$ or $b$ of $P_\sigma(v)$ is $0$. So every term vanishes or cancels.

For the second claim, $\operatorname{Alt}(a \cdot b)(v) = \sum_\sigma P_\sigma(v)$, and the $k! \, l!$ elements of one coset give the same term. $\square$

::: mathlib
`AlternatingMap.domCoprod` · `Mathlib.LinearAlgebra.Alternating.DomCoprod`

For `a : Mᵢ [⋀^ιa]→ₗ[R'] N₁` and `b : Mᵢ [⋀^ιb]→ₗ[R'] N₂`, the map `a.domCoprod b : Mᵢ [⋀^ιa ⊕ ιb]→ₗ[R'] (N₁ ⊗[R'] N₂)`. The sum runs over the cosets `Equiv.Perm.ModSumCongr ιa ιb`. The values lie in the tensor product of Chapter 2, which is $R$ for forms. The factor $k! \, l!$ is `MultilinearMap.domCoprod_alternatization_eq`.

<?decl AlternatingMap.domCoprod?>
:::

### Alternating forms of top degree

Let $M$ be free with a basis $e = (e_1, \dots, e_n)$. For a tuple $v = (v_1, \dots, v_n)$ write $v_j = \sum_i A_{ij} e_i$; the matrix $A$ has the coordinates of $v_j$ in its column $j$. Put $\det_e(v) = \det A$.

**Theorem (Uniqueness of the determinant).** For each $f \in \operatorname{Alt}^n_R(M; N)$ and each tuple $v$, $f(v) = \det_e(v) \, f(e)$. The map $f \mapsto f(e)$ is an isomorphism $\operatorname{Alt}^n_R(M; N) \cong N$. In particular $\operatorname{Alt}^n_R(R^n; R)$ is free of rank $1$ with the basis $\det$.

*Proof.* By the expansion theorem of Section 2,
$$f(v) = \sum_{r} \Big(\prod_{j} A_{r(j) j}\Big) f(e_{r(1)}, \dots, e_{r(n)}),$$
where $r$ runs over all functions $\{1, \dots, n\} \to \{1, \dots, n\}$. If $r$ is not injective, two arguments are equal and the term is $0$. An injective $r$ is a permutation $\sigma$, and $f(e \circ \sigma) = \operatorname{sign}(\sigma) f(e)$. So $f(v) = (\sum_\sigma \operatorname{sign}(\sigma) \prod_j A_{\sigma(j) j}) f(e)$, and the sum is the Leibniz formula for $\det A$ (Volume 7, Chapter 4). So the linear map $f \mapsto f(e)$ is injective. For $z \in N$ the map $v \mapsto \det_e(v) \, z$ is alternating, since $\det$ is multilinear and alternating in the columns, and its value at $e$ is $\det I \cdot z = z$. So the map is surjective. For $M = R^n$ and $N = R$, $\det$ corresponds to $1$. $\square$

**Corollary (Forms of high degree).** If $M$ is free of rank $n$ and $k > n$, then $\operatorname{Alt}^k_R(M; N) = 0$.

*Proof.* In the expansion of $f(v)$ over functions $r : \{1, \dots, k\} \to \{1, \dots, n\}$, no $r$ is injective. So each term is $0$. $\square$

::: mathlib
`Module.Basis.ext_alternating` · `Mathlib.LinearAlgebra.Alternating.Basic`

Two alternating maps are equal if they agree on all tuples `fun i => e (v i)` with `v` injective. The instance `AlternatingMap.uniqueOfCommRing` is the case $M = R$ of the corollary.

<?decl Module.Basis.ext_alternating?>
:::

::: mathlib
`Module.Basis.det` · `Mathlib.LinearAlgebra.Determinant`

The determinant `e.det : M [⋀^ι]→ₗ[R] R` of a basis. The lemma `AlternatingMap.map_basis_eq_zero_iff` says that an alternating form `f` with `f e = 0` is zero. The index of this edition has no declaration for the formula $f = f(e) \det_e$ itself.

<?decl Module.Basis.det?>
<?decl AlternatingMap.map_basis_eq_zero_iff?>
:::

### Examples

**Example (The product of two linear forms).** For $k = l = 1$ the subgroup $S_1 \times S_1$ is trivial, so $(\alpha \wedge \beta)(u, v) = \alpha(u) \beta(v) - \alpha(v) \beta(u)$. On $\mathbb{Q}^3$ take $\alpha = x_1 + x_2$ and $\beta = x_3$, with $u = (1, 0, 2)$ and $v = (0, 1, 1)$. Then $\alpha(u) = 1$, $\beta(v) = 1$, $\alpha(v) = 1$ and $\beta(u) = 2$, so $(\alpha \wedge \beta)(u, v) = 1 - 2 = -1$.

**Counterexample (Antisymmetric but not alternating).** Over $\mathbb{F}_2$ let $f(x, y) = x_1 y_1$ on $\mathbb{F}_2^2$. It is symmetric, and $-1 = 1$, so $f(y, x) = -f(x, y)$. But $f(e_1, e_1) = 1 \neq 0$.

**Counterexample (Torsion in the values).** Over $\mathbb{Z}$ let $M = N = \mathbb{Z}/2$ and $f(x) = x$, alternating of one argument. The family $(1)$ is dependent, since $2 \cdot 1 = 0$, but $f(1) = 1$. So the theorem needs $N$ torsion free.

### The library around it

The map `AlternatingMap.curryLeft` turns $f \in \operatorname{Alt}^{n+1}(M; N)$ into a linear map $M \to \operatorname{Alt}^n(M; N)$, and `AlternatingMap.alternatizeUncurryFin` goes back with alternating signs. Chapter 4 turns alternating maps into linear maps on $\bigwedge^n M$.

### Exercises

1. (A) Let $f$ be alternating. Show that $f(v[i \mapsto v_i + c v_j]) = f(v)$ for $i \neq j$. Hint: expand at the place $i$.
2. (A) Compute $\operatorname{Alt}(m)$ for $m(u, v, w) = u_1 v_2 w_3$ on $R^3$. Hint: the six permutations give the Leibniz formula.
3. (B) Over a field $K$ of characteristic not $2$, show that an antisymmetric bilinear map is alternating. Hint: $2 f(v, v) = 0$.
4. (B) Show that $\dim \operatorname{Alt}^2_K(K^3; K) = 3$. Hint: the values $f(e_i, e_j)$ for $i < j$.
5. (B) List the shuffles for $k = 2$, $l = 1$, and write $(a \wedge \gamma)(u, v, w)$ for a $2$-form $a$ and a $1$-form $\gamma$. Hint: there are $\binom{3}{2} = 3$ shuffles.
6. (C) Let $f \in \operatorname{Alt}^n_R(R^n; R)$ and $A$ an $n \times n$ matrix. Show that $f(A v_1, \dots, A v_n) = \det A \cdot f(v)$, and deduce $\det(AB) = \det A \det B$. Hint: $v \mapsto f(A v)$ is alternating.

### Notes and history

Mathlib defines alternating maps by $v_i = v_j \Rightarrow f(v) = 0$, and not by antisymmetry, so the theory is correct in characteristic $2$. For the same reason the alternatization does not divide by $n!$.

### Reference

<?reference?>
