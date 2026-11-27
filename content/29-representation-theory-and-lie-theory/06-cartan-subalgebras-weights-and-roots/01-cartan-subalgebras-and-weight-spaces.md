---
title: Cartan subalgebras and weight spaces
kind: theory
modules:
  - Mathlib.Algebra.Lie.CartanSubalgebra
  - Mathlib.Algebra.Lie.CartanExists
  - Mathlib.Algebra.Lie.Rank
  - Mathlib.Algebra.Lie.Weights.Basic
  - Mathlib.Algebra.Lie.Weights.Cartan
  - Mathlib.Algebra.Lie.Weights.Linear
explains:
  E3: [LieSubalgebra.IsCartanSubalgebra, LieSubalgebra.isCartanSubalgebra_iff_isUcsLimit, LieAlgebra.exists_isCartanSubalgebra_engel, LieAlgebra.isRegular_iff_finrank_engel_eq_rank, LieModule.genWeightSpace, LieModule.iSupIndep_genWeightSpace, LieModule.iSup_genWeightSpace_eq_top, LieModule.trace_toEnd_genWeightSpace, LieModule.LinearWeights, LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan, LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace]
  E2: [LieSubmodule.IsUcsLimit, LieAlgebra.top_isCartanSubalgebra_of_nilpotent, LieSubalgebra.ne_bot_of_isCartanSubalgebra, LieAlgebra.exists_isCartanSubalgebra_engel_of_finrank_le_card, LieAlgebra.engel_isBot_of_isMin, LieAlgebra.rank, LieModule.rank, LieAlgebra.IsRegular, LieAlgebra.exists_isRegular, LieAlgebra.finrank_engel, LieAlgebra.rank_le_finrank_engel, LieModule.weightSpace, LieModule.genWeightSpaceOf, LieModule.mem_genWeightSpace, LieModule.Weight, LieModule.isCompl_genWeightSpace_zero_posFittingComp, LieModule.IsTriangularizable, LieModule.instLinearWeightsOfCharZero, LieModule.instLinearWeightsOfIsLieAbelian, LieModule.Weight.toLinear, LieModule.exists_forall_lie_eq_smul, LieAlgebra.rootSpace, LieAlgebra.zeroRootSubalgebra, LieAlgebra.rootSpace_zero_eq, LieAlgebra.corootSpace, LieAlgebra.cartan_sup_iSup_rootSpace_eq_top]
  E1: auto
families: []
requires: [V07.C03, V07.C05, V29.C04, V29.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Cartan subalgebras and weight spaces

### Overview

The structure theory of a Lie algebra $L$ starts from a large nilpotent subalgebra $H$. The adjoint action of $H$ splits $L$ into generalized eigenspaces, one for each function $\alpha : H \to K$. These are the root spaces, and the functions that occur are the roots. For $\mathfrak{sl}_2$ with $H$ the diagonal matrices of trace $0$, the root spaces are the lines through $e$, $h$ and $f$.

A Cartan subalgebra is a nilpotent subalgebra equal to its own normalizer. Over an infinite field every finite dimensional Lie algebra has one, namely the Engel subalgebra of a suitable element. For a nilpotent $L$ and an $L$-module $M$, the generalized weight spaces $M_\chi$ are submodules, they are independent, and they fill $M$ when the action is triangularizable. In characteristic $0$ every weight is linear. Applied to $H$ acting on $L$, this gives $L_0 = H$, and the bracket adds roots. Mathlib writes `toEnd R L M x` for the action $\rho(x)$. Chapter 4 gives Lie modules and normalizers, and Chapter 5 gives nilpotency, the central series and Engel's theorem.

### Definitions

**Definition (Cartan subalgebra).** Let $L$ be a Lie algebra over a commutative ring $R$. A Lie subalgebra $H \subseteq L$ is a *Cartan subalgebra* if $H$ is nilpotent and $H$ is self-normalizing: the normalizer $N(H) = \{z \in L : [z, H] \subseteq H\}$ is equal to $H$.

**Definition (Upper central series limit).** For a Lie submodule $N$ of an $L$-module $M$, the normalizer of $N$ is $\{m : [x, m] \in N \text{ for all } x\}$. The upper central series is $Z_0 = 0$, with $Z_{k+1}$ the normalizer of $Z_k$. The submodule $N$ is its *limit* if $Z_l = N$ for all large $l$.

**Definition (Engel subalgebra).** For $x \in L$, the *Engel subalgebra* of $x$ is $E(x) = \{y \in L : (\operatorname{ad} x)^k y = 0 \text{ for some } k\}$. It is a subalgebra that contains $x$.

**Definition (Rank and regular element).** Let $L$ have finite dimension $n$ over a field $K$. For $x \in L$, write $\chi_{\operatorname{ad} x}(T) = T^n + c_{n-1}(x) T^{n-1} + \cdots + c_0(x)$. The *rank* of $L$ is the smallest $r$ such that the coefficient $c_r$, seen as a polynomial function on $L$, is not identically $0$. An element $x$ is *regular* if $c_r(x) \neq 0$.

**Definition (Weight space).** Let $L$ be nilpotent and $M$ an $L$-module. For $\chi : L \to R$, the *weight space* is $\{m : \rho(x) m = \chi(x) m \text{ for all } x\}$, and the *generalized weight space* is
$$M_\chi = \{m \in M : \text{for each } x \in L \text{ there is } k \text{ with } (\rho(x) - \chi(x))^k m = 0\}.$$
For one $x$, write $M_\chi(x)$ for the vectors killed by a power of $\rho(x) - \chi(x)$, so $M_\chi = \bigcap_x M_\chi(x)$.

**Definition (Weight).** A *weight* of $M$ is a function $\chi : L \to R$ with $M_\chi \neq 0$. The module $M$ has *linear weights* if every weight is linear and vanishes on $[L, L]$. It is *triangularizable* if for each $x$ the generalized eigenspaces of $\rho(x)$ span $M$, which always holds over an algebraically closed field.

**Definition (Root space).** Let $H \subseteq L$ be a nilpotent subalgebra. For $\alpha : H \to R$, the *root space* $L_\alpha$ is the generalized weight space of the $H$-module $L$, and a *root* is a weight of this module. The *zero root subalgebra* is $L_0$.

### Theorems and proofs

**Theorem (Cartan subalgebras by the upper central series).** A subalgebra $H \subseteq L$ is a Cartan subalgebra if and only if $H$, as an $H$-submodule of the $H$-module $L$, is the limit of the upper central series of $L$.

*Proof.* Let $Z_k$ be the upper central series of the $H$-module $L$. The normalizer of the submodule $H$ is $\{z : [h, z] \in H \text{ for all } h \in H\} = N(H)$.

Suppose $H$ is a Cartan subalgebra. Step 1: $H$ is nilpotent, so its own upper central series reaches $H$ at some $k$, and it lies inside that of $L$, so $H \subseteq Z_k$. Step 2: by induction, $Z_j \subseteq H$ for all $j$, since $Z_j \subseteq H$ gives $Z_{j+1} \subseteq N(H) = H$. Step 3: so $Z_k = H$, and $Z_{k+1} = N(H) = H$. By induction $Z_l = H$ for all $l \geq k$.

Conversely, suppose $Z_l = H$ for all $l \geq k$. Step 1: $H = Z_{k+1}$ is the normalizer of $Z_k = H$, so $N(H) = H$. Step 2: by the definition of the normalizer, $[H, Z_{i+1}] \subseteq Z_i$ for all $i$. With $C^0(H) = H = Z_k$ and $C^{j+1}(H) = [H, C^j(H)]$, induction gives $C^j(H) \subseteq Z_{k - j}$ for $j \leq k$. For $j = k$ this gives $C^k(H) \subseteq Z_0 = 0$, so $H$ is nilpotent. $\square$

**Proposition (Normalizer of an Engel subalgebra).** For every $x \in L$, the normalizer of $E(x)$ is $E(x)$.

*Proof.* Let $z \in N(E(x))$. Since $x \in E(x)$, $[x, z] \in E(x)$, so $(\operatorname{ad} x)^{k+1} z = (\operatorname{ad} x)^k [x, z] = 0$ for some $k$, and $z \in E(x)$. $\square$

**Theorem (Existence of Cartan subalgebras).** Let $L$ be a Lie algebra of finite dimension $n$ over a field $K$ with $n \leq |K|$. Then there is $x \in L$ such that $E(x)$ is a Cartan subalgebra. In particular this holds over every infinite field.

*Proof.* Step 1: since $L$ is finite dimensional, there is $x$ such that $E(x)$ is minimal for inclusion among all Engel subalgebras. Step 2: by the proposition, $E(x)$ is self-normalizing. Step 3: Barnes' lemma states that if $E(x)$ is minimal and $n \leq |K|$, then $E(x) \subseteq E(y)$ for every $y \in E(x)$. Its proof follows the line $x + t(y - x)$. The determinant of $\operatorname{ad}(x + t(y - x))$ on $L / E(x)$ is a polynomial in $t$ of degree at most $n$ that is nonzero at $t = 0$, so $|K| \geq n$ gives enough values of $t$ to compare the Engel subalgebras along the line, and minimality forces the inclusion. Step 4: let $H = E(x)$. For each $y \in H$, the map $\operatorname{ad} y$ is nilpotent on $E(y) \supseteq H$, so $\operatorname{ad} y$ restricted to $H$ is nilpotent. By Engel's theorem (Chapter 5), $H$ is nilpotent. With Step 2, $H$ is a Cartan subalgebra. $\square$

**Theorem (Regular elements).** Let $L$ be finite dimensional over a field $K$. For every $x$, $\dim E(x)$ is the order of vanishing of $\chi_{\operatorname{ad} x}$ at $0$, so $\operatorname{rank} L \leq \dim E(x)$. Equality holds if and only if $x$ is regular. If $K$ is infinite, a regular element exists.

*Proof.* Step 1: $\dim E(x)$ is the algebraic multiplicity of the eigenvalue $0$ of $\operatorname{ad} x$ (Volume 7, Chapter 5), that is, the smallest $j$ with $c_j(x) \neq 0$. Step 2: then $c_j$ is not identically $0$, so $j \geq r$. Step 3: $\dim E(x) = r$ means $c_r(x) \neq 0$, which is regularity. Step 4: over an infinite field the nonzero polynomial $c_r$ has a point where it does not vanish. $\square$

**Lemma (Weight spaces are submodules).** Let $L$ be nilpotent. For all $\chi$ and $x$, the space $M_\chi(x)$ is a Lie submodule of $M$. So $M_\chi$ is a Lie submodule.

*Proof.* Step 1: as $L$ is nilpotent, $(\operatorname{ad} x)^N = 0$ for some $N$. Step 2: put $a = \rho(x) - \chi(x)$. From $a \rho(y) = \rho(y) a + \rho([x, y])$, induction gives
$$a^n \rho(y) = \sum_{k=0}^{n} \binom{n}{k} \rho\big((\operatorname{ad} x)^k y\big)\, a^{n-k}.$$
Step 3: if $a^K m = 0$, take $n = N + K$. Each term has $k \geq N$ or $n - k > K$, so $a^n [y, m] = 0$. $\square$

**Theorem (Independence of weight spaces).** Let $L$ be nilpotent, $R$ a domain and $M$ torsion free. The generalized weight spaces $M_\chi$ for distinct $\chi$ are independent: a finite sum $\sum m_i = 0$ with $m_i \in M_{\chi_i}$ and distinct $\chi_i$ has all $m_i = 0$.

*Proof.* Take a relation $m_1 + \cdots + m_s = 0$ with all $m_i \neq 0$ and $s \geq 2$ minimal. Step 1: pick $x$ with $c = \chi_2(x) - \chi_1(x) \neq 0$, put $a = \rho(x) - \chi_1(x)$, and choose $K$ with $a^K m_1 = 0$. By the lemma, $a^K$ preserves each $M_{\chi_i}$, so $\sum_{i \geq 2} a^K m_i = 0$ is a shorter relation. Step 2: write $a = b + c$ with $b = \rho(x) - \chi_2(x)$, and let $J$ be minimal with $b^J m_2 = 0$. Then $b^{J-1} a^K m_2 = c^K b^{J-1} m_2 \neq 0$, since $R$ is a domain and $M$ is torsion free. So the shorter relation is nontrivial, a contradiction. $\square$

**Theorem (Weight space decomposition).** Let $L$ be nilpotent over a field $K$ and $M$ finite dimensional and triangularizable. Then $M = \bigoplus_\chi M_\chi$, and $M$ has finitely many weights.

*Proof.* Independence gives the direct sum. For the span, use induction on $\dim M$. Case 1: each $\rho(x)$ has one eigenvalue $\chi(x)$. By triangularizability $M = M_\chi(x)$ for all $x$, so $M = M_\chi$. Case 2: some $\rho(x)$ has two eigenvalues. Then $M = \bigoplus_\lambda M^\lambda$ over the generalized eigenspaces of $\rho(x)$. By the lemma each $M^\lambda$ is a smaller submodule, still triangularizable, and its weight spaces lie in those of $M$. Induction finishes the proof. Independent nonzero subspaces of a finite dimensional space are finite in number. $\square$

**Proposition (Trace on a weight space).** Let $L$ be nilpotent over a field $K$ and $M_\chi$ finite dimensional. For all $x$, $\operatorname{tr}(\rho(x)|_{M_\chi}) = (\dim M_\chi)\, \chi(x)$.

*Proof.* On $M_\chi$ the map $\rho(x) - \chi(x)$ is nilpotent, so its trace is $0$. So $\operatorname{tr} \rho(x) = \operatorname{tr}(\chi(x) \cdot \mathrm{id}) = \dim M_\chi \cdot \chi(x)$. $\square$

**Corollary (Linear weights in characteristic zero).** If $K$ has characteristic $0$, every weight $\chi$ of a finite dimensional $M$ is linear and vanishes on $[L, L]$.

*Proof.* Let $d = \dim M_\chi > 0$. In characteristic $0$, $d$ is invertible and $\chi(x) = d^{-1} \operatorname{tr}(\rho(x)|_{M_\chi})$, a linear function of $x$. A commutator has trace $0$, so $\chi([x, y]) = 0$. $\square$

**Theorem (The bracket adds roots).** Let $H \subseteq L$ be nilpotent and $M$ an $L$-module, seen as an $H$-module. If $x \in L_\alpha$ and $m \in M_\chi$, then $[x, m] \in M_{\alpha + \chi}$.

*Proof.* Fix $h$, and put $a = \operatorname{ad} h - \alpha(h)$ and $b = \rho(h) - \chi(h)$. The Leibniz rule gives $(\rho(h) - \alpha(h) - \chi(h))[x, m] = [a x, m] + [x, b m]$, and by induction
$$(\rho(h) - \alpha(h) - \chi(h))^n [x, m] = \sum_{k=0}^n \binom{n}{k} [a^k x, b^{n-k} m].$$
If $a^A x = 0$ and $b^B m = 0$, take $n = A + B$, and every term is $0$. $\square$

**Theorem (The zero root space of a Cartan subalgebra).** Let $L$ be Noetherian over $R$ and $H \subseteq L$ a nilpotent subalgebra. Then $L_0 = H$ if and only if $H$ is a Cartan subalgebra.

*Proof.* Step 1: $H \subseteq L_0$, since $H$ is nilpotent. Step 2: $N(H) \subseteq L_0$: for $z \in N(H)$ and $h \in H$, $[h, z] \in H \subseteq L_0$, so $(\operatorname{ad} h)^{k+1} z = 0$ for some $k$. Step 3: if $L_0 = H$, Step 2 gives $N(H) = H$. Step 4: let $H$ be a Cartan subalgebra with $H \neq L_0$. Each $h$ acts nilpotently on the nonzero Noetherian $H$-module $Q = L_0 / H$. By Engel's theorem for modules (Chapter 5) there is $0 \neq \bar z \in Q$ killed by $H$. A lift $z$ has $[H, z] \subseteq H$, so $z \in N(H) = H$ and $\bar z = 0$, a contradiction. $\square$

### Examples

**Example (The diagonal Cartan subalgebra of sl2).** Let $L = \mathfrak{sl}_2(K)$ with $h = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$, $e = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$, $f = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$ and $\operatorname{char} K \neq 2$. Then $[h, e] = 2e$, $[h, f] = -2f$ and $[e, f] = h$. The line $H = K h$ is abelian. For $z = a e + b h + c f$, $[h, z] = 2a e - 2c f$, and this lies in $H$ only if $a = c = 0$. So $N(H) = H$ and $H$ is a Cartan subalgebra. The roots are $0$ and $\pm \alpha$ with $\alpha(t h) = 2t$, with $L_{\alpha} = K e$, $L_0 = H$ and $L_{-\alpha} = K f$. The natural module $K^2$ has the weights $\pm \omega$ with $\omega(t h) = t$, and $[e, K^2_{-\omega}] \subseteq K^2_{\omega}$, as the theorem on adding roots predicts.

**Example (Rank of sl2).** For $x = \begin{pmatrix} a & b \\ c & -a \end{pmatrix}$ in $\mathfrak{sl}_2(K)$, $\operatorname{char} K \neq 2$, the map $\operatorname{ad} x$ has the eigenvalues $0$ and $\pm 2\sqrt{a^2 + bc}$ in a splitting field, and $\chi_{\operatorname{ad} x}(T) = T^3 - 4(a^2 + bc) T$. So $c_0 = 0$ identically and $c_1 = -4(a^2 + bc) = 4 \det x$ is not. The rank is $1$, and $x$ is regular if and only if $\det x \neq 0$. So $E(h) = K h$, while $\operatorname{ad} e$ is nilpotent and $E(e) = L$.

**Counterexample (A weight that is not linear).** Let $K = \mathbb{F}_2$ and $L = \mathfrak{sl}_2(\mathbb{F}_2)$. Here $[h, e] = 2e = 0$, $[h, f] = 0$ and $[e, f] = h$, so $L$ is a Heisenberg algebra, hence nilpotent. Let $L$ act on $M = \mathbb{F}_2^2$. For $x = \begin{pmatrix} a & b \\ c & a \end{pmatrix}$, the Cayley and Hamilton theorem gives $x^2 = \det(x) I = (a + bc) I$, using $a^2 = a$ in $\mathbb{F}_2$. So $(x - \lambda)^2 = (a + bc + \lambda) I$, and $M = M_\chi$ for the single function $\chi(x) = a + bc$. This $\chi$ is a weight, but $\chi(e) = \chi(f) = 0$ and $\chi(e + f) = 1$, so $\chi$ is not additive. Here $\dim M_\chi = 2 = 0$ in $K$, so the trace argument fails.

### The library around it

::: mathlib
`LieSubalgebra.IsCartanSubalgebra` · `Mathlib.Algebra.Lie.CartanSubalgebra`

The class has the fields `nilpotent` and `self_normalizing : H.normalizer = H`. `LieSubmodule.IsUcsLimit` is the limit condition, and `isCartanSubalgebra_iff_isUcsLimit` applies it to `H.toLieSubmodule`, the subalgebra as an `H`-submodule of `L`. The instance `LieAlgebra.top_isCartanSubalgebra_of_nilpotent` treats a nilpotent `L`, and `ne_bot_of_isCartanSubalgebra` excludes `⊥`. A splitting Cartan subalgebra is expressed by adding `LieModule.IsTriangularizable R H L`.

<?decl LieSubalgebra.IsCartanSubalgebra?>
:::

::: mathlib
`LieAlgebra.exists_isCartanSubalgebra_engel` · `Mathlib.Algebra.Lie.CartanExists`

The statement is `∃ x, (LieSubalgebra.engel K x).IsCartanSubalgebra` over an `[Infinite K]`, and `exists_isCartanSubalgebra_engel_of_finrank_le_card` takes `finrank K L ≤ #K` instead. Barnes' lemma is `engel_isBot_of_isMin`. The Engel subalgebra, `normalizer_engel` and `isNilpotent_of_forall_le_engel` live in `Mathlib.Algebra.Lie.EngelSubalgebra`.

<?decl LieAlgebra.exists_isCartanSubalgebra_engel?>
:::

::: mathlib
`LieAlgebra.isRegular_iff_finrank_engel_eq_rank` · `Mathlib.Algebra.Lie.Rank`

`LieModule.rank` is defined through the characteristic polynomial of `toEnd` over the polynomial ring of the coordinates, and `LieAlgebra.rank` is the adjoint case. `finrank_engel`, `rank_le_finrank_engel` and this equivalence are Steps 1 to 3 of the theorem, and `exists_isRegular` is Step 4.

<?decl LieAlgebra.isRegular_iff_finrank_engel_eq_rank?>
:::

::: mathlib
`LieModule.genWeightSpace` · `Mathlib.Algebra.Lie.Weights.Basic`

`genWeightSpace M χ` is the infimum of `genWeightSpaceOf M (χ x) x`, unfolded by `mem_genWeightSpace`, and `weightSpace M χ` is the true weight space. `LieModule.Weight R L M` bundles a function `L → R` with the proof that its space is not `⊥`. `iSupIndep_genWeightSpace` is the independence theorem, `iSup_genWeightSpace_eq_top` the decomposition under `[IsTriangularizable K L M]`, and `trace_toEnd_genWeightSpace` the trace formula. `isCompl_genWeightSpace_zero_posFittingComp` is the Fitting decomposition $M = M_0 \oplus M^{+}$.

<?decl LieModule.genWeightSpace?>
:::

::: mathlib
`LieModule.LinearWeights` · `Mathlib.Algebra.Lie.Weights.Linear`

The class asks `map_add`, `map_smul` and `map_lie` of every weight. The instance `instLinearWeightsOfCharZero` is the corollary, and `instLinearWeightsOfIsLieAbelian` covers an abelian `L`. `Weight.toLinear` gives an element of `L →ₗ[R] R`, and `exists_forall_lie_eq_smul` gives a common eigenvector.

<?decl LieModule.LinearWeights?>
:::

::: mathlib
`LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan` · `Mathlib.Algebra.Lie.Weights.Cartan`

`rootSpace H χ` abbreviates `genWeightSpace L χ` for the `H`-module `L`, and `zeroRootSubalgebra R L H` is `rootSpace H 0` as a subalgebra. `rootSpace_zero_eq` states $L_0 = H$ for a Cartan subalgebra. `lie_mem_genWeightSpace_of_mem_genWeightSpace` is the theorem on adding roots. `corootSpace α`, the span of $[L_\alpha, L_{-\alpha}]$ in $H$, is used in Section 2, and `cartan_sup_iSup_rootSpace_eq_top` states $L = H + \sum_{\alpha \neq 0} L_\alpha$.

<?decl LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan?>
:::

Common errors of a learner: The first error is to read `genWeightSpace` as the space of true eigenvectors; `weightSpace` is that space. The second error is to expect a weight to be a linear map; `LieModule.Weight R L M` is built from a bare function, and linearity comes from `LinearWeights`, as the example over $\mathbb{F}_2$ requires. The third error is to forget that `rootSpace H χ` needs `[LieRing.IsNilpotent H]`, which comes from `IsCartanSubalgebra` only when that instance is in scope. The fourth error is to forget triangularizability: $\mathfrak{so}_2$ acting on $\mathbb{R}^2$ has no weights.

### Exercises

1. (A) Show that the diagonal matrices of trace $0$ form a Cartan subalgebra of $\mathfrak{sl}_3(\mathbb{C})$. Hint: compute $[\operatorname{diag}(t_1, t_2, t_3), E_{ij}] = (t_i - t_j) E_{ij}$ and choose $t$ with distinct entries.
2. (A) Show that the strictly upper triangular matrices in $\mathfrak{sl}_2(\mathbb{C})$ form a nilpotent subalgebra that is not a Cartan subalgebra. Hint: find its normalizer.
3. (A) Find the rank of a nilpotent Lie algebra $L$ and its regular elements. Hint: every $\operatorname{ad} x$ is nilpotent, so $\chi_{\operatorname{ad} x} = T^n$.
4. (B) Let $L$ be the two dimensional algebra with $[x, y] = y$. Find all Cartan subalgebras of $L$ over $\mathbb{C}$. Hint: a Cartan subalgebra here is a line $K(x + c y)$; check the normalizer.
5. (B) Prove that the Engel subalgebra $E(x)$ is a subalgebra. Hint: expand $(\operatorname{ad} x)^n [y, z]$ by the Leibniz rule.
6. (B) Let $H = \mathbb{C} h$ in $\mathfrak{sl}_2(\mathbb{C})$ act on the homogeneous polynomials of degree $n$ in $X, Y$, with $h = X \partial_X - Y \partial_Y$. Find the weights. Hint: $X^{n-k} Y^k$ has weight $t h \mapsto (n - 2k) t$.
7. (C) Let $L$ be nilpotent and $M$ finite dimensional over a field. Show that $M_0$ is the union of the upper central series $Z_k$ of $M$. Hint: $\rho(x_1) \cdots \rho(x_k)$ kills $Z_k$, and for the converse apply Engel's theorem to the module $M_0$.

### Notes and history

Killing found the roots of a Lie algebra as the roots of the characteristic polynomial of $\operatorname{ad} x$ for a general $x$, and Cartan made the theory rigorous in his thesis of 1894. The existence proof through a minimal Engel subalgebra is due to Barnes (1967). The weight space decomposition for a nilpotent Lie algebra is central in Jacobson's book of 1962, and Bourbaki's Chapter VII treats positive characteristic, with the example over $\mathbb{F}_2$.

The Mathlib files are by these authors, read from their headers: `CartanSubalgebra`, `Weights.Basic`, `Weights.Cartan` and `Weights.Linear` by Oliver Nash; `CartanExists` and `Rank` by Johan Commelin.

### Reference

<?reference?>
