---
title: The Chinese remainder theorem and prime avoidance
kind: theory
modules: []
explains:
  E3: [Ideal.quotientInfRingEquivPiQuotient, Ideal.subset_union_prime]
  E2: [Ideal.prod_eq_iInf_of_pairwise_isCoprime, Ideal.quotientInfToPiQuotient, Ideal.quotientInfToPiQuotient_surj, Ideal.quotientInfToPiQuotient_inj, Ideal.exists_forall_sub_mem_ideal, Ideal.isCoprime_biInf, Ideal.subset_union, Ideal.subset_union_prime_finite, "Ideal.subset_union_prime'", Ideal.IsPrime.prod_le, Ideal.IsPrime.inf_le, "Ideal.IsPrime.inf_le'", CompleteOrthogonalIdempotents]
  E1: auto
families: []
requires: [V06.C02, V06.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Chinese remainder theorem and prime avoidance

### Overview

Volume 6, Chapter 2 proved the Chinese remainder theorem for two ideals. This section proves it for finitely many ideals, with the converse: the canonical map is surjective only when the ideals are pairwise coprime. The theorem also produces orthogonal idempotents, and Lagrange interpolation is a special case.

The second half proves prime avoidance: an ideal contained in a finite union of prime ideals is contained in one of them. The section uses the rules for coprime ideals of Section 1. Rings are commutative with $1$.

### Definitions

**Definition (Pairwise coprime).** Ideals $I_1, \dots, I_n$ of $R$ are pairwise coprime if $I_i + I_j = R$ for all $i \ne j$.

**Definition (Canonical map).** For ideals $I_1, \dots, I_n$ of $R$, the canonical map is
$$\varphi : R \to R/I_1 \times \dots \times R/I_n, \qquad x \mapsto (x + I_1, \dots, x + I_n).$$
It is a ring homomorphism with kernel $I_1 \cap \dots \cap I_n$.

**Definition (Orthogonal idempotents).** An element $e$ is idempotent if $e^2 = e$. Elements $e_1, \dots, e_n$ form a complete set of orthogonal idempotents if each $e_i$ is idempotent, $e_i e_j = 0$ for $i \ne j$, and $e_1 + \dots + e_n = 1$.

In $R_1 \times \dots \times R_n$, the elements $\varepsilon_i$ with $1$ in place $i$ and $0$ elsewhere form a complete set of orthogonal idempotents.

### Theorems and proofs

**Lemma (Coprime to a product).** If $I$ is coprime to each of $J_1, \dots, J_n$, then $I$ is coprime to $J_1 \cdots J_n$ and to $J_1 \cap \dots \cap J_n$.

*Proof.* By Section 1, $I + J_1 = R$ and $I + J_2 = R$ give $I + J_1 J_2 = R$. Induction on $n$ gives $I + J_1 \cdots J_n = R$. Since $J_1 \cdots J_n \subseteq J_1 \cap \dots \cap J_n$, also $I + \bigcap_i J_i = R$. $\square$

**Theorem (Product and intersection).** If $I_1, \dots, I_n$ are pairwise coprime, then $I_1 \cdots I_n = I_1 \cap \dots \cap I_n$.

*Proof.* Induction on $n$. The case $n = 1$ is clear. Let $n \ge 2$ and $K = I_1 \cdots I_{n - 1}$, which equals $I_1 \cap \dots \cap I_{n - 1}$ by induction. By the lemma, $I_n + K = R$. For coprime ideals the product equals the intersection (Volume 6, Chapter 2), so $K I_n = K \cap I_n = I_1 \cap \dots \cap I_n$. $\square$

::: mathlib
`Ideal.prod_eq_iInf_of_pairwise_isCoprime` · `Mathlib.RingTheory.Ideal.Operations`

The theorem for a `Finset` of indices: `(↑s).Pairwise (Function.onFun IsCoprime J) → ∏ i ∈ s, J i = ⨅ i ∈ s, J i`. The lemma is `Ideal.isCoprime_biInf`.

<?decl Ideal.prod_eq_iInf_of_pairwise_isCoprime?>
:::

**Theorem (Chinese remainder theorem).** Let $I_1, \dots, I_n$ be ideals of $R$ and $\varphi$ the canonical map.

1. $\varphi$ induces an injective homomorphism $\bar\varphi : R / (I_1 \cap \dots \cap I_n) \to \prod_i R/I_i$.
2. $\varphi$ is surjective if and only if the $I_i$ are pairwise coprime.
3. If the $I_i$ are pairwise coprime, then $R/(I_1 \cdots I_n) = R/(I_1 \cap \dots \cap I_n) \cong \prod_i R/I_i$.

*Proof.* (1) The kernel of $\varphi$ is $\bigcap_i I_i$. Apply the first isomorphism theorem (Volume 6, Chapter 2).

(2) Let the $I_i$ be pairwise coprime and fix $i$. By the lemma $I_i + \prod_{j \ne i} I_j = R$, so $1 = a_i + e_i$ with $a_i \in I_i$ and $e_i \in \prod_{j \ne i} I_j$. Then $e_i \equiv 1 \pmod{I_i}$ and $e_i \equiv 0 \pmod{I_j}$ for $j \ne i$. Given $x_1, \dots, x_n \in R$, put $x = x_1 e_1 + \dots + x_n e_n$. Then $x \equiv x_i \pmod{I_i}$ for each $i$, so $\varphi(x) = (x_1 + I_1, \dots, x_n + I_n)$.

Conversely let $\varphi$ be surjective and $i \ne j$. Choose $x$ with $\varphi(x) = \varepsilon_i$, so $x - 1 \in I_i$ and $x \in I_j$. Then $1 = (1 - x) + x \in I_i + I_j$.

(3) Combine (1), (2) and the previous theorem. $\square$

::: mathlib
`Ideal.quotientInfRingEquivPiQuotient` · `Mathlib.RingTheory.Ideal.Quotient.Operations`

Part (3) for a finite index type `ι`: `R ⧸ ⨅ i, f i ≃+* ((i : ι) → R ⧸ f i)`, with the hypothesis `Pairwise (Function.onFun IsCoprime f)`. The map `Ideal.quotientInfToPiQuotient` is injective in general (`Ideal.quotientInfToPiQuotient_inj`) and surjective for pairwise coprime ideals (`Ideal.quotientInfToPiQuotient_surj`). The form with elements is `Ideal.exists_forall_sub_mem_ideal`.

<?decl Ideal.quotientInfRingEquivPiQuotient?>
:::

**Theorem (Idempotents and products).** Let $e \in R$ be idempotent. Then $(e)$ and $(1 - e)$ are coprime, $(e) \cap (1 - e) = 0$, and
$$R \cong R/(1 - e) \times R/(e).$$
More generally, a complete set of orthogonal idempotents $e_1, \dots, e_n$ gives $R \cong \prod_i R/(1 - e_i)$, and a ring isomorphism $R \cong R_1 \times \dots \times R_n$ gives the complete set $e_i = \psi^{-1}(\varepsilon_i)$.

*Proof.* $e + (1 - e) = 1$, so the ideals are coprime. By the theorem on products, $(e) \cap (1 - e) = (e)(1 - e) = (e - e^2) = 0$. The Chinese remainder theorem gives the isomorphism.

For the general case, $1 - e_i = \sum_{j \ne i} e_j$. For $i \ne j$, $e_j (1 - e_i) = e_j - e_j e_i = e_j$, so $e_j \in (1 - e_i)$, and $1 = e_j + (1 - e_j)$ with $e_j \in (1 - e_i)$ shows $(1 - e_i) + (1 - e_j) = R$. If $x \in \bigcap_i (1 - e_i)$, then $x e_i \in (1 - e_i) e_i = 0$ for each $i$, so $x = \sum_i x e_i = 0$. Apply the Chinese remainder theorem. The last claim holds because $\psi^{-1}$ is a ring isomorphism and the $\varepsilon_i$ have the three properties. $\square$

::: mathlib
`CompleteOrthogonalIdempotents` · `Mathlib.RingTheory.Idempotents`

`CompleteOrthogonalIdempotents e` for a family `e : I → R` with `Fintype I` says that the `e i` are idempotent (`IsIdempotentElem`, Volume 5), pairwise orthogonal, and sum to `1`.

<?decl CompleteOrthogonalIdempotents?>
:::

**Theorem (Prime avoidance).** Let $P_1, \dots, P_n$ be ideals of $R$, all of them prime except at most two. If an ideal $I$ satisfies $I \subseteq P_1 \cup \dots \cup P_n$, then $I \subseteq P_i$ for some $i$.

*Proof.* Induction on $n$. The case $n = 1$ is clear. Let $n \ge 2$, and suppose that $I \not\subseteq P_i$ for each $i$. If $I$ lies in the union of $n - 1$ of the $P_i$, then the induction hypothesis gives a contradiction, since that subfamily also has at most two ideals that are not prime. So for each $i$ there is $x_i \in I$ with $x_i \notin P_j$ for all $j \ne i$. Since $x_i \in I \subseteq \bigcup_j P_j$, it follows that $x_i \in P_i$.

Case $n = 2$. Let $y = x_1 + x_2 \in I$. If $y \in P_1$, then $x_2 = y - x_1 \in P_1$, a contradiction. In the same way $y \notin P_2$. So $y \in I$ lies in no $P_i$, a contradiction.

Case $n \ge 3$. At least one $P_i$ is prime. Renumber so that $P_n$ is prime, and let $y = x_n + x_1 x_2 \cdots x_{n - 1} \in I$. For $i < n$, the product $x_1 \cdots x_{n - 1}$ lies in $P_i$ since $x_i \in P_i$, so $y \in P_i$ would give $x_n \in P_i$, a contradiction. If $y \in P_n$, then $x_1 \cdots x_{n - 1} = y - x_n \in P_n$, and since $P_n$ is prime some $x_i$ with $i < n$ lies in $P_n$, a contradiction. So $y$ lies in no $P_i$. $\square$

::: mathlib
`Ideal.subset_union_prime` · `Mathlib.RingTheory.Ideal.Operations`

The theorem for a `Finset` `s` of indices and two exceptional indices `a b`, stated as an equivalence. The case of two ideals is `Ideal.subset_union`, the version for a finite `Set` is `Ideal.subset_union_prime_finite`, and `Ideal.subset_union_prime'` is the induction step.

<?decl Ideal.subset_union_prime?>
:::

**Corollary (Primes over an intersection).** Let $P$ be prime and $I_1 \cap \dots \cap I_n \subseteq P$. Then $I_i \subseteq P$ for some $i$. If $P = I_1 \cap \dots \cap I_n$, then $P = I_i$ for some $i$.

*Proof.* If $I_i \not\subseteq P$ for each $i$, choose $x_i \in I_i \setminus P$. Then $x_1 \cdots x_n \in \bigcap_i I_i \subseteq P$, and primality gives some $x_i \in P$, a contradiction. If $P = \bigcap_i I_i$, then $P \subseteq I_i \subseteq P$ for the index found. $\square$

The library states the corollary as `Ideal.IsPrime.inf_le'` for a finite infimum, `Ideal.IsPrime.inf_le` for two ideals, and `Ideal.IsPrime.prod_le` for a product.

### Examples

**Example (The ring $\mathbb{Z}/360$).** Since $360 = 8 \cdot 9 \cdot 5$ with pairwise coprime factors, $\mathbb{Z}/360 \cong \mathbb{Z}/8 \times \mathbb{Z}/9 \times \mathbb{Z}/5$. The proof asks for $e_1 \equiv 1 \pmod 8$ with $45 \mid e_1$, and so on, which gives $e_1 = 225$, $e_2 = 280$, $e_3 = 216$, with sum $721 \equiv 1 \pmod{360}$. To solve $x \equiv 3 \pmod 8$, $x \equiv 2 \pmod 9$, $x \equiv 4 \pmod 5$, take
$$x = 3 \cdot 225 + 2 \cdot 280 + 4 \cdot 216 = 2099 \equiv 299 \pmod{360}.$$
Check: $299 = 37 \cdot 8 + 3 = 33 \cdot 9 + 2 = 59 \cdot 5 + 4$.

**Example (Lagrange interpolation).** Let $k$ be a field and $a_1, \dots, a_n \in k$ distinct. The ideals $(x - a_i)$ of $k[x]$ are pairwise coprime, since $(x - a_i) - (x - a_j) = a_j - a_i$ is a unit. The theorem gives $k[x]/\prod_i (x - a_i) \cong k^n$, $f \mapsto (f(a_1), \dots, f(a_n))$, and $e_i = \prod_{j \ne i} (x - a_j)/(a_i - a_j)$. Over $\mathbb{Q}$, with the points $0, 1, 2$ and the values $1, 3, 7$:
$$f = \tfrac{1}{2}(x - 1)(x - 2) - 3 x (x - 2) + \tfrac{7}{2} x (x - 1) = x^2 + x + 1.$$

**Counterexample (Prime avoidance needs primes).** Let $R = \mathbb{F}_2[x, y]/(x, y)^2$ and $\mathfrak{m} = (x, y)/(x, y)^2 = \{0, x, y, x + y\}$. Each product of two elements of $\mathfrak{m}$ is $0$, so $(x) = \{0, x\}$, $(y) = \{0, y\}$ and $(x + y) = \{0, x + y\}$. Then $\mathfrak{m} = (x) \cup (y) \cup (x + y)$, but $\mathfrak{m}$ lies in none of the three. None of the three is prime: $y \cdot y = 0 \in (x)$ and $y \notin (x)$. With three exceptional ideals the theorem fails.

### The library around it

Common errors:

- `Ideal.quotientInfRingEquivPiQuotient` needs `Finite ι`. For a `Finset` of ideals, use the subtype of the `Finset` as the index type.
- `Ideal.subset_union_prime` asks for primality outside two indices `a b`. When all ideals are prime, any two indices of `s` serve as `a b`.

### Exercises

1. (A) Find the idempotents of $\mathbb{Z}/30$ that the proof gives for $30 = 2 \cdot 3 \cdot 5$, and solve $x \equiv 1 \pmod 2$, $x \equiv 2 \pmod 3$, $x \equiv 3 \pmod 5$.
2. (A) Show that $\mathbb{Z}/4 \not\cong \mathbb{Z}/2 \times \mathbb{Z}/2$, and explain which hypothesis fails.
3. (B) Show that a ring $R$ has an idempotent $e \ne 0, 1$ if and only if $R \cong R_1 \times R_2$ with $R_1, R_2$ nonzero.
4. (B) Show that $\mathbb{R}[x]/(x^4 - 1) \cong \mathbb{R} \times \mathbb{R} \times \mathbb{C}$. Hint: $x^4 - 1 = (x - 1)(x + 1)(x^2 + 1)$.
5. (B) Let $P_1, \dots, P_n$ be primes and $I \not\subseteq P_i$ for each $i$. Show that there is $x \in I$ that lies in no $P_i$.
6. (C) Let $R$ have finitely many maximal ideals $\mathfrak{m}_1, \dots, \mathfrak{m}_n$, and let $J(R) = 0$. Show that $R$ is a product of $n$ fields.
7. (C) Let $k$ be an infinite field and $V_1, \dots, V_n$ proper subspaces of a $k$-vector space $V$. Show that $V \ne V_1 \cup \dots \cup V_n$. Hint: for a minimal $n$, choose $u \in V_1$ outside $V_2 \cup \dots \cup V_n$ and $v \notin V_1$, and look at $v + \lambda u$ for $n$ distinct $\lambda \in k$.

### Notes and history

The theorem on simultaneous congruences appears in the Chinese text *Sunzi Suanjing*. Atiyah and Macdonald, Chapter 1, prove prime avoidance for prime ideals only.

### Reference

<?reference?>
