---
title: Finite root systems, bases and Cartan matrices
kind: theory
modules:
  - Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
  - Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
  - Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
  - Mathlib.LinearAlgebra.RootSystem.RootPositive
  - Mathlib.LinearAlgebra.RootSystem.Chain
  - Mathlib.LinearAlgebra.RootSystem.Base
  - Mathlib.LinearAlgebra.RootSystem.BaseExists
  - Mathlib.LinearAlgebra.RootSystem.CartanMatrix
explains:
  E3: [RootPairing.RootForm, RootPairing.rootForm_reflection_reflection_apply, RootPairing.four_smul_rootForm_sq_eq_coxeterWeight_smul, RootPairing.rootForm_nondegenerate, RootPairing.rootForm_pos_of_ne_zero, RootPairing.InvariantForm, RootPairing.InvariantForm.two_mul_apply_root_root, RootPairing.coxeterWeightIn_mem_set_of_isCrystallographic, RootPairing.pairingIn_pairingIn_mem_set_of_isCrystallographic, RootPairing.root_sub_root_mem_of_pairingIn_pos, RootPairing.root_add_zsmul_mem_range_iff, RootPairing.chainBotCoeff_sub_chainTopCoeff, RootPairing.chainBotCoeff_add_chainTopCoeff_le_three, RootPairing.Base, RootPairing.Base.pairingIn_le_zero_of_ne, RootPairing.nonempty_base, RootPairing.Base.cartanMatrix, RootPairing.Base.cartanMatrix_isFiniteCartan]
  E2: [RootPairing.Polarization, RootPairing.rootForm_self_sum_of_squares, RootPairing.posRootForm, RootPairing.IsAnisotropic, RootPairing.RootPositiveForm, RootPairing.InvariantForm.pairing_mul_eq_pairing_mul_swap, RootPairing.coxeterWeight_nonneg, RootPairing.coxeterWeightIn_le_four, RootPairing.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed, RootPairing.root_add_root_mem_of_pairingIn_neg, RootPairing.chainTopCoeff, RootPairing.chainBotCoeff, RootPairing.Base.sub_notMem_range_root, RootPairing.Base.height, RootPairing.Base.IsPos, RootPairing.Base.cartanMatrix_mem_of_ne, RootPairing.Base.cartanMatrix_eq_neg_chainTopCoeff, RootPairing.Base.equivOfCartanMatrixEq, RootPairing.baseOf_pairwise_pairing_le_zero]
  E1: auto
families: []
requires: [V07.C02, V08.C05, V08.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Finite root systems, bases and Cartan matrices

### Overview

A finite root pairing carries a canonical symmetric bilinear form, built from the coroots and preserved by every reflection. Over $\mathbb{Q}$ or $\mathbb{R}$ it is positive definite, so it replaces the Euclidean inner product of the classical theory. It bounds the Coxeter weight $c_{ij} = p_{ij}p_{ji}$ of a crystallographic pairing by $4$, and this bound controls the rest: the pairings take few values, root chains have no gaps and length at most $3$, and simple roots exist.

A base is a set of simple roots, and the pairings between simple roots form the Cartan matrix, which determines a reduced root system. The examples are the Cartan matrices of $A_2$, $B_2$ and $G_2$. The notation is that of Section 1: roots $\alpha_i \in M$, coroots $\alpha_i^\vee \in N$ and $p_{ij} = \langle \alpha_i, \alpha_j^\vee \rangle$. Throughout, $\iota$ is finite.

### Definitions

**Definition (Root form).** The *root form* of $P$ is the bilinear form on $M$ given by $B(x, y) = \sum_k \langle x, \alpha_k^\vee \rangle \langle y, \alpha_k^\vee \rangle$. The *polarization* is the linear map $\Pi : M \to N$, $\Pi(x) = \sum_k \langle x, \alpha_k^\vee \rangle\, \alpha_k^\vee$, so $B(x, y) = \langle y, \Pi(x) \rangle$.

**Definition (Invariant form).** An *invariant form* is a symmetric bilinear form $B$ on $M$ such that every reflection $s_i$ preserves $B$ and $B(\alpha_i, \alpha_i) \neq 0$ for all $i$. A *root positive form* for an ordered subring $S$ also takes values in $S$ on pairs of roots, with $B(\alpha_i, \alpha_i) > 0$.

**Definition (Root chain).** For independent roots $\alpha = \alpha_i$ and $\beta = \alpha_j$, the *top coefficient* $q$ (the *bottom coefficient* $r$) is the largest $n \geq 0$ such that $\beta + n\alpha$ (respectively $\beta - n\alpha$) is a root. The *$\alpha$-chain through $\beta$* is the set of roots $\beta + z\alpha$, $z \in \mathbb{Z}$.

**Definition (Base).** A *base* of $P$ is a finite set $\Delta \subseteq \iota$ such that the roots $\alpha_i$, $i \in \Delta$, are linearly independent, the coroots $\alpha_i^\vee$, $i \in \Delta$, are linearly independent, every root lies in $\mathbb{N}\Delta$ or in $-\mathbb{N}\Delta$, and every coroot lies in $\mathbb{N}\Delta^\vee$ or in $-\mathbb{N}\Delta^\vee$. Here $\mathbb{N}\Delta$ is the set of sums $\sum_{i \in \Delta} n_i \alpha_i$ with $n_i \in \mathbb{N}$. The roots $\alpha_i$, $i \in \Delta$, are the *simple roots*. If $\alpha_k = \sum z_i \alpha_i$, the *height* of $\alpha_k$ is $\sum z_i$, and $\alpha_k$ is *positive* if its height is positive.

**Definition (Cartan matrix).** The *Cartan matrix* of a base $\Delta$ of a crystallographic pairing is the integer matrix $A = (A_{ij})_{i, j \in \Delta}$ with $A_{ij} = p_{ij} = \langle \alpha_i, \alpha_j^\vee \rangle$.

**Definition (Finite Cartan matrix).** An integer square matrix $A$ is a *finite type Cartan matrix* if $A_{ii} = 2$, $A_{ij} \leq 0$ for $i \neq j$, $A_{ij} = 0$ if and only if $A_{ji} = 0$, and there are integers $d_i > 0$ such that $\operatorname{diag}(d)\,A$ is positive definite.

### Theorems and proofs

**Proposition (The root form is invariant).** $B(s_i x, s_i y) = B(x, y)$ for all $i$, $x$ and $y$.

*Proof.* Step 1: $s_i^\vee$ is the transpose of $s_i$ (Section 1), so $\langle s_i x, \alpha_k^\vee \rangle = \langle x, s_i^\vee \alpha_k^\vee \rangle = \langle x, \alpha_{\sigma_i(k)}^\vee \rangle$. Step 2: then $B(s_i x, s_i y) = \sum_k \langle x, \alpha_{\sigma_i(k)}^\vee \rangle \langle y, \alpha_{\sigma_i(k)}^\vee \rangle$, and since $\sigma_i$ is a permutation of $\iota$, this sum is $B(x, y)$. $\square$

**Lemma (Pairings and an invariant form).** If $B$ is symmetric and preserved by the reflections, then $2B(\alpha_i, \alpha_j) = p_{ij}\,B(\alpha_j, \alpha_j)$. Consequently $p_{ji}B(\alpha_i, \alpha_i) = p_{ij}B(\alpha_j, \alpha_j)$ and $4B(\alpha_i, \alpha_j)^2 = c_{ij}\,B(\alpha_i, \alpha_i)\,B(\alpha_j, \alpha_j)$.

*Proof.* Step 1: $s_j \alpha_i = \alpha_i - p_{ij}\alpha_j$ and $s_j \alpha_j = -\alpha_j$. Invariance gives $B(\alpha_i, \alpha_j) = B(\alpha_i - p_{ij}\alpha_j, -\alpha_j) = -B(\alpha_i, \alpha_j) + p_{ij}B(\alpha_j, \alpha_j)$, which is the first claim. Step 2: exchange $i$ and $j$ and use symmetry: $p_{ij}B(\alpha_j, \alpha_j) = 2B(\alpha_i, \alpha_j) = p_{ji}B(\alpha_i, \alpha_i)$. Step 3: multiply the two forms of Step 2: $4B(\alpha_i, \alpha_j)^2 = p_{ij}p_{ji}B(\alpha_i, \alpha_i)B(\alpha_j, \alpha_j)$. $\square$

**Theorem (Positivity).** Over an ordered field, the root form of a finite root system satisfies $B(x, x) > 0$ for $x \neq 0$.

*Proof.* Step 1: $B(x, x) = \sum_k \langle x, \alpha_k^\vee \rangle^2 \geq 0$ as a sum of squares. Step 2: if $B(x, x) = 0$, every term is $0$, so $\langle x, \alpha_k^\vee \rangle = 0$ for all $k$. The coroots span $N$, so $\langle x, n \rangle = 0$ for all $n \in N$, and $x = 0$ since the pairing is perfect. $\square$

**Theorem (Crystallographic restriction).** Let $P$ be a finite crystallographic root pairing over a field of characteristic $0$. Then $c_{ij} \in \{0, 1, 2, 3, 4\}$, and $c_{ij} = 4$ only for linearly dependent roots. If $P$ is reduced and $\alpha_i \neq \pm\alpha_j$, the pair $(p_{ij}, p_{ji})$ is one of $(0, 0)$, $\pm(1, 1)$, $\pm(1, 2)$, $\pm(2, 1)$, $\pm(1, 3)$, $\pm(3, 1)$.

*Proof.* Step 1: the $\mathbb{Q}$-spans of the roots and coroots carry a finite root system over $\mathbb{Q}$ with the same $p_{ij}$ (Mathlib's `restrictScalarsRat`). So assume $R = \mathbb{Q}$. Step 2: by positivity, $B(\alpha_i, \alpha_i) > 0$ for all $i$. The lemma gives $p_{ji}B(\alpha_i, \alpha_i) = p_{ij}B(\alpha_j, \alpha_j)$, so $p_{ij}$ and $p_{ji}$ have the same sign and $c_{ij} \geq 0$. Step 3 (Cauchy and Schwarz): put $a = B(\alpha_i, \alpha_i)$, $b = B(\alpha_i, \alpha_j)$, $d = B(\alpha_j, \alpha_j)$ and $v = a\alpha_j - b\alpha_i$. Then $0 \leq B(v, v) = a^2 d - 2ab^2 + b^2 a = a(ad - b^2)$, so $b^2 \leq ad$. Step 4: the lemma gives $c_{ij}\,ad = 4b^2 \leq 4ad$, and $ad > 0$, so $c_{ij} \leq 4$. Since $c_{ij}$ is an integer, $c_{ij} \in \{0, \ldots, 4\}$. Step 5: Section 1 proved that $c_{ij} = 4$ if and only if the roots are dependent. Step 6: if $P$ is reduced and $\alpha_i \neq \pm \alpha_j$, the roots are independent, so $p_{ij}p_{ji} \in \{0, 1, 2, 3\}$ with equal signs, and $p_{ij} = 0$ if and only if $p_{ji} = 0$ by Step 2. Factor $1$, $2$ and $3$. $\square$

The lemma also shows that if $p_{ij} \neq 0$, then $B(\alpha_i, \alpha_i)/B(\alpha_j, \alpha_j) = p_{ij}/p_{ji}$, which in the reduced case is $1$, $2$, $3$, $1/2$ or $1/3$. For irreducible reduced systems, `InvariantForm.apply_eq_or` and `forall_pairing_eq_swap_or` refine this to two root lengths.

**Proposition (Differences of roots).** In a finite crystallographic root pairing over a field of characteristic $0$, if $i \neq j$ and $p_{ij} > 0$, then $\alpha_i - \alpha_j$ is a root.

*Proof.* Step 1: $\alpha_i \neq \alpha_j$ by injectivity, and $\alpha_i \neq -\alpha_j$ since $p_{ij} > 0$. Step 2: if the roots are dependent, then, as in the proof of Section 1, $\alpha_i = t\alpha_j$ with $p_{ij} = 2t$ and $p_{ji} = 2/t$, two positive integers with product $4$. The case $t = 1$ is excluded, so $\alpha_i = 2\alpha_j$ or $\alpha_j = 2\alpha_i$. In the first case $\alpha_i - \alpha_j = \alpha_j$, in the second $\alpha_i - \alpha_j = -\alpha_i = s_i\alpha_i$; both are roots. Step 3: if the roots are independent, $c_{ij} \in \{1, 2, 3\}$, so $p_{ij} = 1$ or $p_{ji} = 1$. If $p_{ij} = 1$, then $s_j\alpha_i = \alpha_i - \alpha_j$ is a root. If $p_{ji} = 1$, then $s_i\alpha_j = \alpha_j - \alpha_i$ is a root, and so is its negative. $\square$

Applied to $\alpha_i$ and $-\alpha_j$, the proposition gives: if $p_{ij} < 0$ and $\alpha_i \neq -\alpha_j$, then $\alpha_i + \alpha_j$ is a root.

**Theorem (Root chains).** Let $P$ be as in the proposition, and let $\alpha = \alpha_i$ and $\beta = \alpha_j$ be independent. Then $\beta + z\alpha$ is a root exactly for the integers $z$ with $-r \leq z \leq q$, and $r - q = \langle \beta, \alpha^\vee \rangle$. If $P$ is reduced, $r + q \leq 3$.

*Proof.* Step 1: the set $Z = \{z : \beta + z\alpha \text{ is a root}\}$ is finite and contains $0$. If it is not an interval, there are $s < t$ in $Z$ with $t \geq s + 2$ and no element strictly between them. Put $\gamma = \beta + s\alpha$ and $\delta = \beta + t\alpha$. Step 2: $\gamma + \alpha$ is not a root and $\gamma \neq -\alpha$ by independence, so the remark after the proposition gives $\langle \gamma, \alpha^\vee \rangle \geq 0$. In the same way $\delta - \alpha$ is not a root, so $\langle \delta, \alpha^\vee \rangle \leq 0$. Step 3: but $\langle \delta, \alpha^\vee \rangle = \langle \gamma, \alpha^\vee \rangle + 2(t - s) > 0$, a contradiction. So $Z$ is the interval $[-r, q]$. Step 4: $s_\alpha(\beta + z\alpha) = \beta - (\langle \beta, \alpha^\vee \rangle + z)\alpha$, so $z \mapsto -\langle \beta, \alpha^\vee \rangle - z$ maps $Z$ onto $Z$. It reverses the order, so it sends $q$ to $-r$, which gives $r - q = \langle \beta, \alpha^\vee \rangle$. Step 5: apply Step 4 to the bottom root $\beta' = \beta - r\alpha$, whose chain has bottom coefficient $0$ and top coefficient $r + q$: $\langle \beta', \alpha^\vee \rangle = -(r + q)$. In the reduced case the restriction bounds $|\langle \beta', \alpha^\vee \rangle|$ by $3$. $\square$

**Proposition (Simple roots).** Let $\Delta$ be a base of a finite crystallographic pairing over a field of characteristic $0$, and $i \neq j$ in $\Delta$. Then $\alpha_i - \alpha_j$ is not a root, and $p_{ij} \leq 0$.

*Proof.* Step 1: if $\alpha_i - \alpha_j = \alpha_k$, then by independence the coefficients of $\alpha_k$ are $1$ at $i$ and $-1$ at $j$, of mixed signs, which contradicts the definition of a base. Step 2: if $p_{ij} > 0$, the proposition on differences makes $\alpha_i - \alpha_j$ a root, which Step 1 excludes. $\square$

**Theorem (Existence of a base).** A finite, reduced, crystallographic root system over a field of characteristic $0$ has a base.

*Proof.* As in the restriction theorem, the problem reduces to $R = \mathbb{Q}$, where $B$ is positive definite. Step 1: a $\mathbb{Q}$-vector space is not a finite union of proper subspaces, so some linear form $f$ has $f(\alpha_k) \neq 0$ for all $k$. Call $\alpha_k$ positive if $f(\alpha_k) > 0$; since $-\alpha_k$ is a root, every root is positive or its negative is. Step 2: let $\Delta$ be the set of positive roots that are not the sum of two positive roots. Every positive root lies in $\mathbb{N}\Delta$: otherwise take a counterexample $\gamma$ with $f(\gamma)$ least; $\gamma \notin \Delta$, so $\gamma = \gamma_1 + \gamma_2$ with $\gamma_1, \gamma_2$ positive and $f(\gamma_1), f(\gamma_2) < f(\gamma)$, and both lie in $\mathbb{N}\Delta$, a contradiction. Step 3: for distinct $\alpha, \beta \in \Delta$, $\alpha - \beta$ is not a root: if it were positive, $\alpha = \beta + (\alpha - \beta)$ would not be in $\Delta$, and if it were negative, $\beta = \alpha + (\beta - \alpha)$ would not be. By the proposition on differences, $\langle \alpha, \beta^\vee \rangle \leq 0$, and by the lemma $B(\alpha, \beta) \leq 0$. Step 4: suppose $\sum_{\alpha \in \Delta} c_\alpha \alpha = 0$. Split the sum by the sign of $c_\alpha$ to get $v = \sum_{c_\alpha > 0} c_\alpha \alpha = \sum_{c_\beta < 0} (-c_\beta)\beta$. Then $B(v, v) = \sum c_\alpha(-c_\beta)B(\alpha, \beta) \leq 0$, so $v = 0$. Then $0 = f(v) = \sum_{c_\alpha > 0} c_\alpha f(\alpha)$ with all $f(\alpha) > 0$, so no $c_\alpha$ is positive, and likewise none is negative. So $\Delta$ is independent. Step 5: the conditions on coroots hold because, in a reduced system, the same $\Delta$ is the set of indecomposable positive coroots for a suitable form on $N$; this text does not reproduce Mathlib's proof, `baseOf_root_eq_baseOf_coroot`. $\square$

**Theorem (The Cartan matrix is of finite type).** Let $P$ be a finite crystallographic root system over a field of characteristic $0$ and $\Delta$ a base. Then the Cartan matrix $A$ is a finite type Cartan matrix, and $A_{ij} \in \{0, -1, -2, -3\}$ for $i \neq j$.

*Proof.* Step 1: $A_{ii} = p_{ii} = 2$. Step 2: for $i \neq j$, $A_{ij} \leq 0$ by the proposition on simple roots. The simple roots are independent, so the restriction theorem gives $c_{ij} \leq 3$, and $A_{ij} \geq -3$. Step 3: by the lemma, $A_{ij} = 0$ if and only if $B(\alpha_i, \alpha_j) = 0$, which is symmetric in $i$ and $j$. Step 4: reduce to $\mathbb{Q}$ and let $G_{ij} = B(\alpha_i, \alpha_j)$ be the Gram matrix of the simple roots and $D = \operatorname{diag}(1/G_{jj})$. The lemma says $A = 2\,G D$, so $DA = 2\,DGD$. The matrix $G$ is positive definite because $B$ is and the simple roots are independent, so $DGD$ is positive definite. Multiplying $D$ by a common denominator gives positive integers $d_i$. $\square$

### Examples

The coordinates are those of Section 1.

**Example (A2).** The simple roots are $\alpha_1 = \varepsilon_1 - \varepsilon_2$ and $\alpha_2 = \varepsilon_2 - \varepsilon_3$, for $f(x) = 3x_1 + 2x_2 + x_3$. The positive roots are $\alpha_1$, $\alpha_2$ and $\alpha_1 + \alpha_2 = \varepsilon_1 - \varepsilon_3$, of heights $1$, $1$ and $2$. The Cartan matrix is $\begin{pmatrix} 2 & -1 \\ -1 & 2 \end{pmatrix}$, and with $d = (1, 1)$ it is positive definite, with determinant $3$. The $\alpha_1$-chain through $\alpha_2$ is $\alpha_2, \alpha_2 + \alpha_1$: $r = 0$, $q = 1$, and $r - q = -1 = p_{21}$.

**Example (B2).** Take $\alpha_1 = \varepsilon_1 - \varepsilon_2$ (long) and $\alpha_2 = \varepsilon_2$ (short). The positive roots are $\alpha_1$, $\alpha_2$, $\alpha_1 + \alpha_2 = \varepsilon_1$ and $\alpha_1 + 2\alpha_2 = \varepsilon_1 + \varepsilon_2$. The Cartan matrix is $A = \begin{pmatrix} 2 & -2 \\ -1 & 2 \end{pmatrix}$, since $p_{12} = -2$ and $p_{21} = -1$. The $\alpha_2$-chain through $\alpha_1$ is $\alpha_1, \alpha_1 + \alpha_2, \alpha_1 + 2\alpha_2$, with $r - q = -2 = p_{12}$. With $d = (1, 2)$, $\operatorname{diag}(d)A = \begin{pmatrix} 2 & -2 \\ -2 & 4 \end{pmatrix}$, of determinant $4 > 0$.

**Example (G2).** Take $\alpha_1 = \varepsilon_1 - \varepsilon_2$ (short) and $\alpha_2 = -2\varepsilon_1 + \varepsilon_2 + \varepsilon_3$ (long). The six positive roots are the short roots $\alpha_1$, $\alpha_1 + \alpha_2 = \varepsilon_3 - \varepsilon_1$, $2\alpha_1 + \alpha_2 = \varepsilon_3 - \varepsilon_2$ and the long roots $\alpha_2$, $3\alpha_1 + \alpha_2 = \varepsilon_1 - 2\varepsilon_2 + \varepsilon_3$, $3\alpha_1 + 2\alpha_2 = -\varepsilon_1 - \varepsilon_2 + 2\varepsilon_3$; the last one has height $5$. The $\alpha_1$-chain through $\alpha_2$ is $\alpha_2, \ldots, \alpha_2 + 3\alpha_1$, of the maximal length $3$, with $r - q = -3 = p_{21}$. The Cartan matrix is $A = \begin{pmatrix} 2 & -1 \\ -3 & 2 \end{pmatrix}$. With $d = (3, 1)$, $\operatorname{diag}(d)A = \begin{pmatrix} 6 & -3 \\ -3 & 2 \end{pmatrix}$, of determinant $3 > 0$.

**Counterexample (A base needs coroots).** The non-reduced system $BC_1$ in $\mathbb{Q}$ has roots $\pm 1$, $\pm 2$ with coroots $\pm 2$, $\pm 1$. A base has one element, and up to sign the candidates are $\Delta = \{1\}$ and $\Delta = \{2\}$. For $\Delta = \{1\}$ the coroot $\pm 1$ of the root $\pm 2$ is not in $\pm\mathbb{N} \cdot 2$; for $\Delta = \{2\}$ the root $\pm 1$ is not in $\pm\mathbb{N} \cdot 2$. The negative candidates fail in the same way. So no base exists in Mathlib's sense, although the classical definition accepts $\{1\}$.

### The library around it

::: mathlib
`RootPairing.RootForm` · `Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear`

`P.RootForm` is `∑ i, (P.coroot' i).smulRight (P.coroot' i)`, and `Polarization` is $\Pi$. Invariance is `rootForm_reflection_reflection_apply`. The lemma is `InvariantForm.two_mul_apply_root_root` for a bundled `InvariantForm`, and its Step 3 for the root form is `four_smul_rootForm_sq_eq_coxeterWeight_smul`.

<?decl RootPairing.RootForm?>
:::

::: mathlib
`RootPairing.rootForm_pos_of_ne_zero` · `Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate`

Over a linearly ordered commutative ring, the root form is positive on nonzero vectors of the root span. `rootForm_nondegenerate` needs `IsRootSystem`, and `IsAnisotropic` asks only $B(\alpha_i, \alpha_i) \neq 0$.

<?decl RootPairing.rootForm_pos_of_ne_zero?>
:::

::: mathlib
`RootPairing.pairingIn_pairingIn_mem_set_of_isCrystallographic` · `Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas`

The list of pairs, with the dependent cases $\pm(1, 4)$, $\pm(4, 1)$, $\pm(2, 2)$. The bound $c_{ij} \leq 4$ is `coxeterWeightIn_le_four`, the reduced list is `pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed`, and differences are `root_sub_root_mem_of_pairingIn_pos`.

<?decl RootPairing.pairingIn_pairingIn_mem_set_of_isCrystallographic?>
:::

::: mathlib
`RootPairing.root_add_zsmul_mem_range_iff` · `Mathlib.LinearAlgebra.RootSystem.Chain`

The chain is unbroken: `P.root j + z • P.root i ∈ range P.root` if and only if `z ∈ Icc (-chainBotCoeff i j) (chainTopCoeff i j)`. Note the order: `i` is $\alpha$ and `j` is $\beta$. Then `chainBotCoeff_sub_chainTopCoeff` gives $r - q$ as `P.pairingIn ℤ j i`.

<?decl RootPairing.root_add_zsmul_mem_range_iff?>
:::

::: mathlib
`RootPairing.nonempty_base` · `Mathlib.LinearAlgebra.RootSystem.BaseExists`

The existence theorem, for `[Field R] [CharZero R] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]` and finite `ι`. The base is `baseOf P.root f` for `f : M →+ ℚ` nonzero on the roots.

<?decl RootPairing.nonempty_base?>
:::

::: mathlib
`RootPairing.Base.cartanMatrix_isFiniteCartan` · `Mathlib.LinearAlgebra.RootSystem.CartanMatrix`

`b.cartanMatrix` is the matrix of `P.pairingIn ℤ i j` on `b.support`, and this theorem gives `Matrix.IsFiniteCartan`. The entries are in $\{-3, -2, -1, 0\}$ off the diagonal by `cartanMatrix_mem_of_ne`, and `cartanMatrix_eq_neg_chainTopCoeff` reads $-A_{ij}$ as a top coefficient. By `equivOfCartanMatrixEq`, two reduced root systems with bases of the same Cartan matrix are isomorphic; this text does not prove it.

<?decl RootPairing.Base.cartanMatrix_isFiniteCartan?>
:::

Common errors of a learner: The first error is to transpose the Cartan matrix. Mathlib's `cartanMatrix i j` is $\langle \alpha_i, \alpha_j^\vee \rangle$: for $B_2$ with $\alpha_1$ long it is `CartanMatrix.B 2`, and for $G_2$ with $\alpha_1$ short it is the transpose of `CartanMatrix.G₂`. The second error is to expect a base as a set of roots; `Base` has a field `support : Finset ι` of indices. The third error is to forget that `chainTopCoeff` has junk value $0$ for dependent roots. The fourth error is to apply positivity of `RootForm` over $\mathbb{C}$; Mathlib uses `posRootForm`, valued in an ordered subring such as $\mathbb{Z}$.

### Exercises

1. (A) Compute the root form of $A_2$ on $\alpha_1$ and $\alpha_2$, and show that it is $6$ times the dot product on the plane $x_1 + x_2 + x_3 = 0$. Hint: $B(\alpha_1, \alpha_1) = \sum_k p_{1k}^2$ over the six roots.
2. (A) Find all the root chains of $B_2$ through $\alpha_1$, and check $r - q = \langle \beta, \alpha^\vee \rangle$ in each case. Hint: use $\alpha = \alpha_2$ and $\alpha = \alpha_1 + \alpha_2$.
3. (A) Show that $\{\alpha_1, \alpha_1 + \alpha_2\}$ is not a base of $A_2$. Hint: write $\alpha_2$ in terms of it.
4. (B) Show that if $p_{ij} = p_{ji} = -1$, then $s_i s_j s_i = s_j s_i s_j$. Hint: both are the reflection in $\alpha_i + \alpha_j$; compute $s_i(\alpha_j)$.
5. (B) Let $A$ be a $2 \times 2$ finite type Cartan matrix. Show that $A_{12}A_{21} \in \{0, 1, 2, 3\}$. Hint: $\det(\operatorname{diag}(d)A) > 0$ gives $4 > A_{12}A_{21}$.
6. (C) Prove that every positive root of a reduced system is a simple root or $s_i\beta$ for a positive root $\beta$ of smaller height and a simple $\alpha_i$. Hint: if $\gamma$ is positive and not simple, $B(\gamma, \gamma) > 0$ forces $\langle \gamma, \alpha_i^\vee \rangle > 0$ for some simple $\alpha_i$; then $s_i\gamma = \gamma - \langle \gamma, \alpha_i^\vee \rangle\alpha_i$.

### Notes and history

Killing and Cartan classified the root configurations of the complex simple Lie algebras. The Cartan matrix is the input of Serre's presentation of 1966, used in Section 3, and Mathlib cites Serre's book for `baseOf_pairwise_pairing_le_zero`. For reduced systems Mathlib's base agrees with the classical notion, as the header of `RootSystem.Base` explains.

The Mathlib files are by these authors, read from their headers: `Finite.CanonicalBilinear`, `Finite.Nondegenerate` and `RootPositive` by Scott Carnahan; `Finite.Lemmas`, `Chain`, `Base`, `BaseExists` and `CartanMatrix` by Oliver Nash.

### Reference

<?reference?>
