---
title: Diagonalization and Sylvester's law of inertia
kind: theory
modules:
  - Mathlib.LinearAlgebra.QuadraticForm.Basis
  - Mathlib.LinearAlgebra.QuadraticForm.Real
  - Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
  - Mathlib.LinearAlgebra.QuadraticForm.Radical
  - Mathlib.LinearAlgebra.QuadraticForm.Signature
explains:
  E3: [QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared, sigPos, QuadraticForm.sigPos_of_equiv_weightedSumSquares]
  E2: [sigNeg, QuadraticMap.Equivalent.sigPos_eq, QuadraticMap.Equivalent.sigNeg_eq, QuadraticForm.sigPos_weightedSumSquares, QuadraticForm.sigNeg_weightedSumSquares, QuadraticForm.sigPos_add_finrank_le_of_nonpos, QuadraticForm.sigPos_add_sigNeg_add_radical, le_sigPos_of_posDef, QuadraticMap.radical, QuadraticMap.radical_eq_ker_polarBilin, QuadraticForm.radical_weightedSumSquares, QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed, QuadraticForm.equivalent_of_isAlgClosed, QuadraticForm.equivalent_one_neg_one_weighted_sum_squared, QuadraticMap.toBilin]
  E1: auto
families: []
requires: [V08.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Diagonalization and Sylvester's law of inertia

### Overview

Over a field in which $2 \neq 0$, each quadratic form becomes a weighted sum of squares $w_1 x_1^2 + \dots + w_n x_n^2$ in a suitable basis. The weights are not unique: $x^2$ and $4 x^2$ are equivalent. Over $\mathbb{R}$, Sylvester's law of inertia says that the numbers of positive and of negative weights are intrinsic, and that they classify real forms.

The section uses Section 1 and the orthogonal bases of Chapter 5, Section 2.

### Definitions

Let $K$ be a field and let $Q$ be a quadratic form on a finite-dimensional $K$-vector space $V$.

**Definition (Radical).** The radical of $Q$ is the subspace of the $x \in V$ with $Q(x) = 0$ and $\operatorname{polar}_Q(x, y) = 0$ for all $y$. The rank of $Q$ is $\dim V - \dim \operatorname{rad} Q$.

When $2 \neq 0$ in $K$, the condition $Q(x) = 0$ follows from the second, since $2 Q(x) = \operatorname{polar}_Q(x, x)$. Then the radical is the kernel of the polar, which is the radical of the associated form of Section 1.

::: mathlib
`QuadraticMap.radical` · `Mathlib.LinearAlgebra.QuadraticForm.Radical`

The submodule `{x | Q x = 0 ∧ polarBilin Q x = 0}`; with `Invertible 2`, `radical_eq_ker_polarBilin` drops the first condition. `QuadraticMap.Nondegenerate` adds a condition that matters only in characteristic 2.

<?decl QuadraticMap.radical?>
:::

<?decl QuadraticMap.radical_eq_ker_polarBilin?>

<?decl QuadraticMap.Nondegenerate?>

**Definition (Positive and negative index).** Let $K$ be an ordered field, for example $\mathbb{R}$. The positive index $p(Q)$ is the largest dimension of a subspace $W \subseteq V$ such that $Q|_W$ is positive definite. The negative index is $q(Q) = p(-Q)$. The signature of $Q$ is the pair $(p(Q), q(Q))$.

The zero subspace qualifies, so the maximum exists. The definition uses no basis, so equivalent forms have the same $p$ and $q$.

::: mathlib
`sigPos` · `Mathlib.LinearAlgebra.QuadraticForm.Signature`

The maximum of `finrank` over the submodules on which `Q` restricts to a positive definite form, in the root namespace. The invariance is `QuadraticMap.Equivalent.sigPos_eq`; `le_sigPos_of_posDef` bounds it from below.

<?decl sigPos?>
:::

<?decl sigNeg?>

<?decl QuadraticMap.Equivalent.sigPos_eq?>

<?decl QuadraticMap.Equivalent.sigNeg_eq?>

<?decl le_sigPos_of_posDef?>

::: mathlib
`QuadraticMap.toBilin` · `Mathlib.LinearAlgebra.QuadraticForm.Basis`

For a basis indexed by a linearly ordered type, the upper triangular bilinear map of Section 1, whose diagonal is `Q` in every characteristic.

<?decl QuadraticMap.toBilin?>
:::

### Theorems and proofs

**Theorem (Diagonalization).** Suppose $2 \neq 0$ in $K$. There is a basis $v_1, \dots, v_n$ of $V$ and weights $w_i \in K$ with
$$Q\Big(\sum_i x_i v_i\Big) = \sum_i w_i x_i^2.$$
So $Q$ is equivalent to the weighted sum of squares with the weights $w_i$.

*Proof.* Let $B$ be the associated form of $Q$; it is symmetric with $B(x, x) = Q(x)$ by Section 1. By the orthogonal basis theorem of Chapter 5, Section 2, there is a basis $v_1, \dots, v_n$ with $B(v_i, v_j) = 0$ for $i \neq j$. Put $w_i = Q(v_i) = B(v_i, v_i)$. Then
$$Q\Big(\sum_i x_i v_i\Big) = \sum_{i, j} x_i x_j B(v_i, v_j) = \sum_i w_i x_i^2.$$
The coordinate map $V \to K^n$ is an isometric isomorphism onto the weighted sum of squares. $\square$

<?decl QuadraticForm.equivalent_weightedSumSquares?>

**Proposition (Radical of a diagonal form).** In the situation of the theorem, the radical of $Q$ is spanned by the $v_i$ with $w_i = 0$. So the rank of $Q$ is the number of nonzero weights.

*Proof.* The polar is $\operatorname{polar}_Q(x, y) = 2 \sum_i w_i x_i y_i$. A vector $x$ is in the radical if and only if $\operatorname{polar}_Q(x, v_j) = 2 w_j x_j = 0$ for all $j$, that is, $x_j = 0$ whenever $w_j \neq 0$. $\square$

<?decl QuadraticForm.radical_weightedSumSquares?>

**Corollary (Algebraically closed fields).** If $K$ is algebraically closed with $2 \neq 0$, then each quadratic form of rank $r$ is equivalent to $x_1^2 + \dots + x_r^2$. Two forms on $V$ are equivalent if and only if they have the same rank.

*Proof.* Diagonalize, and order the basis so that $w_1, \dots, w_r$ are the nonzero weights. Pick $c_i$ with $c_i^2 = w_i$ and replace $v_i$ by $v_i / c_i$; the new weight is $w_i / c_i^2 = 1$. Equivalent forms have the same rank, since an isometric isomorphism maps the radical onto the radical. $\square$

::: mathlib
`QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed` · `Mathlib.LinearAlgebra.QuadraticForm.AlgClosed`

If the associated form is separating, `Q` is equivalent to the sum of all squares, and `equivalent_of_isAlgClosed` compares two such forms.

<?decl QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed?>
:::

<?decl QuadraticForm.equivalent_of_isAlgClosed?>

**Corollary (Real forms).** Each real quadratic form on $V$ is equivalent to a form
$$x_1^2 + \dots + x_p^2 - x_{p+1}^2 - \dots - x_{p+q}^2$$
for some $p, q \ge 0$ with $p + q \le n$.

*Proof.* Diagonalize and replace $v_i$ by $v_i / \sqrt{|w_i|}$ when $w_i \neq 0$; the new weight is $w_i / |w_i| = \pm 1$. Reorder the basis so that the weights $1$ come first, then the weights $-1$, then the weights $0$. $\square$

::: mathlib
`QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared` · `Mathlib.LinearAlgebra.QuadraticForm.Real`

Weights `w i ∈ {-1, 0, 1}`, not sorted, with `Q` equivalent to `weightedSumSquares ℝ w`; `equivalent_one_neg_one_weighted_sum_squared` is the nondegenerate case.

<?decl QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared?>
:::

<?decl QuadraticForm.equivalent_one_neg_one_weighted_sum_squared?>

**Lemma (Nonpositive subspaces).** Let $K$ be an ordered field and let $U \subseteq V$ be a subspace with $Q(x) \le 0$ for all $x \in U$. Then $p(Q) + \dim U \le \dim V$.

*Proof.* Let $W$ be a subspace with $Q|_W$ positive definite and $\dim W = p(Q)$. If $x \in W \cap U$ and $x \neq 0$, then $Q(x) > 0$ and $Q(x) \le 0$, which is impossible. So $W \cap U = 0$, and $\dim W + \dim U = \dim(W + U) \le \dim V$. $\square$

<?decl QuadraticForm.sigPos_add_finrank_le_of_nonpos?>

**Theorem (Sylvester's law of inertia).** Let $Q$ be a quadratic form on a real vector space $V$ of dimension $n$, and let $v_1, \dots, v_n$ be a basis with $Q(\sum_i x_i v_i) = \sum_i w_i x_i^2$. Let $p$ be the number of $i$ with $w_i > 0$, $q$ the number with $w_i < 0$, and $r$ the number with $w_i = 0$. Then
$$p = p(Q), \qquad q = q(Q), \qquad r = \dim \operatorname{rad} Q.$$
So $p$, $q$ and $r$ do not depend on the diagonalizing basis, and $p(Q) + q(Q) + \dim \operatorname{rad} Q = n$.

*Proof.* Let $I_+$, $I_-$ and $I_0$ be the sets of indices with $w_i > 0$, $w_i < 0$ and $w_i = 0$. Let $V_+$, $V_-$ and $V_0$ be the spans of the corresponding $v_i$; their dimensions are $p$, $q$ and $r$.

First, $p(Q) \ge p$. For $x = \sum_{i \in I_+} x_i v_i \neq 0$, $Q(x) = \sum_{i \in I_+} w_i x_i^2 > 0$, since each term is $\ge 0$ and some $x_i \neq 0$ gives a positive term. So $Q|_{V_+}$ is positive definite, and $\dim V_+ = p$.

Next, $p(Q) \le p$. Let $U = V_- + V_0$, of dimension $q + r = n - p$. For $x = \sum_{i \notin I_+} x_i v_i$, $Q(x) = \sum_{i \in I_-} w_i x_i^2 \le 0$. By the lemma, $p(Q) + (n - p) \le n$, so $p(Q) \le p$.

The same two steps for $-Q$, whose weights are $-w_i$, give $q(Q) = q$. Finally $r = \dim \operatorname{rad} Q$ by the proposition on the radical of a diagonal form. The sum is $p + q + r = n$. $\square$

::: mathlib
`QuadraticForm.sigPos_of_equiv_weightedSumSquares` · `Mathlib.LinearAlgebra.QuadraticForm.Signature`

If `Q` is equivalent to `weightedSumSquares 𝕜 w` over an ordered field, then `sigPos Q` is `{i | 0 < w i}.ncard`. The negative and radical parts are `sigNeg_weightedSumSquares` and `sigPos_add_sigNeg_add_radical`.

<?decl QuadraticForm.sigPos_of_equiv_weightedSumSquares?>
:::

<?decl QuadraticForm.sigPos_weightedSumSquares?>

<?decl QuadraticForm.sigNeg_weightedSumSquares?>

<?decl QuadraticForm.sigPos_add_sigNeg_add_radical?>

**Corollary (Classification of real forms).** Two real quadratic forms on $V$ are equivalent if and only if they have the same signature.

*Proof.* Equivalent forms have the same $p(Q)$ and $q(Q)$, since the definitions use no basis. Conversely, by the corollary on real forms and the law of inertia, a form of signature $(p, q)$ is equivalent to the form with $p$ weights $1$, $q$ weights $-1$ and $n - p - q$ weights $0$. Two forms of the same signature are equivalent to the same form. $\square$

### Examples

**Example (The signature of $x^2 + y^2 - z^2$).** On $\mathbb{R}^3$ let $Q(x, y, z) = x^2 + y^2 - z^2$. The standard basis diagonalizes $Q$ with the weights $(1, 1, -1)$, so the law of inertia gives $p = 2$, $q = 1$, $r = 0$. Directly: $Q(a, b, 0) = a^2 + b^2 > 0$ for $(a, b) \neq 0$, so $p(Q) \ge 2$; on $U = \mathbb{R} e_3$, $Q \le 0$, so the lemma gives $p(Q) \le 3 - 1 = 2$. The same argument for $-Q$ gives $q(Q) = 1$, and the polar has the invertible matrix $\operatorname{diag}(2, 2, -2)$, so the radical is $0$. The signature is $(2, 1)$.

**Example (A full diagonalization).** On $\mathbb{R}^3$ let
$$Q(x, y, z) = x^2 + 2 x y + 2 y^2 + 2 y z - z^2.$$
Completing squares, first in $x$ and then in $y$:
$$Q = (x + y)^2 + y^2 + 2 y z - z^2 = (x + y)^2 + (y + z)^2 - 2 z^2.$$
In the coordinates $u = x + y$, $v = y + z$, $w = z$, from a matrix of determinant $1$, $Q = u^2 + v^2 - 2 w^2$, and with $w' = \sqrt{2}\, w$, $Q = u^2 + v^2 - w'^2$. So $Q$ is equivalent to $x^2 + y^2 - z^2$, with signature $(2, 1)$. As a check, the associated matrix $\begin{pmatrix} 1 & 1 & 0 \\ 1 & 2 & 1 \\ 0 & 1 & -1 \end{pmatrix}$ has determinant $-2$, the product of the weights.

**Counterexample (The signature does not classify over $\mathbb{Q}$).** The forms $x^2 + y^2$ and $x^2 + 2 y^2$ on $\mathbb{Q}^2$ are positive definite, with signature $(2, 0)$. Their associated matrices have the determinants $1$ and $2$, which differ by a factor that is not a square in $\mathbb{Q}$. By the discriminant corollary of Chapter 5, Section 1, the forms are not equivalent over $\mathbb{Q}$. Over $\mathbb{R}$ they are equivalent by $y \mapsto y / \sqrt 2$.

### The library around it

The invariants `sigPos` and `sigNeg` are in `Mathlib.LinearAlgebra.QuadraticForm.Signature`, the normal forms in the files `.Real` and `.AlgClosed`. The index of this edition has no declaration for the classification of quadratic forms over $\mathbb{Q}$ or over finite fields.

### Exercises

1. (A) Find the signature of $Q(x, y) = x y$ on $\mathbb{R}^2$. Hint: $4 x y = (x + y)^2 - (x - y)^2$.
2. (A) Diagonalize $Q(x, y, z) = x^2 + 4 x y + 3 y^2 + z^2$ over $\mathbb{R}$ and give its signature. Hint: complete the square in $x$.
3. (A) Show that $p(Q) + q(Q) \le \dim V$ for each real form. Hint: a positive definite and a negative definite subspace meet in $0$.
4. (B) Diagonalize $Q(x, y, z) = x y + y z + z x$ over $\mathbb{R}$ and find its signature. Hint: first substitute $x = u + v$, $y = u - v$.
5. (B) Show that a real form $Q$ is positive definite if and only if $p(Q) = \dim V$. Hint: use the lemma with $U$ spanned by one vector.
6. (C) Let $Q$ be a real nondegenerate form with signature $(p, q)$. Show that the largest dimension of a totally isotropic subspace, a subspace on which $Q$ is zero, is $\min(p, q)$. Hint: the lemma and its analogue for $-Q$.

### Notes and history

Sylvester stated the law of inertia in 1852. The classification of quadratic forms over $\mathbb{Q}$ uses the Hasse-Minkowski theorem, which compares the forms over $\mathbb{R}$ and over all fields of $p$-adic numbers.

### Reference

<?reference?>
