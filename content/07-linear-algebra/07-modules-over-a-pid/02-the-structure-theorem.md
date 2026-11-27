---
title: The Smith normal form and the structure theorem
kind: theory
modules:
  - Mathlib.Algebra.Module.PID
  - Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
  - Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
explains:
  E3: [Module.equiv_free_prod_directSum, Submodule.smithNormalForm, Module.equiv_directSum_of_isTorsion]
  E2: [Module.Basis.SmithNormalForm, Submodule.isInternal_prime_power_torsion_of_pid, Submodule.quotientEquivPiZMod, Submodule.quotientEquivDirectSum, AddSubgroup.index_eq_natAbs_det, Ideal.exists_smith_normal_form]
  E1: auto
families: []
requires: [V07.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Smith normal form and the structure theorem

### Overview

Each finitely generated module $M$ over a PID $R$ is a direct sum of cyclic modules:
$$M \cong R^r \oplus R/(d_1) \oplus \dots \oplus R/(d_k), \qquad d_1 \mid d_2 \mid \dots \mid d_k,$$
with $d_i$ nonzero nonunits. Equivalently, $M \cong R^r \oplus \bigoplus_i R/(p_i^{e_i})$ with primes $p_i$. For $R = \mathbb{Z}$ this classifies the finitely generated abelian groups. For $R = K[X]$ it gives the normal forms of a square matrix.

The key step is the Smith normal form: for a submodule $N$ of $R^n$, there is a basis $e_1, \dots, e_n$ of $R^n$ and scalars $d_1, \dots, d_k$ such that $d_1 e_1, \dots, d_k e_k$ is a basis of $N$. This section proves the Smith normal form for matrices over $\mathbb{Z}$ by row and column operations, derives the structure theorem, and computes the quotient $\mathbb{Z}^2 / \langle (2, 4), (6, 8) \rangle$.

### Definitions

**Definition (Smith normal form of a matrix).** An $m \times n$ matrix $D$ over $R$ is in Smith normal form if $D_{ij} = 0$ for $i \neq j$ and its diagonal is $d_1, \dots, d_k, 0, \dots, 0$ with $d_i \neq 0$ and $d_1 \mid d_2 \mid \dots \mid d_k$. The $d_i$ are the invariant factors.

**Definition (Smith normal form of a submodule).** Let $M$ be free with a finite basis and $N \subseteq M$. A Smith normal form of $N$ is a basis $(e_i)_{i \in I}$ of $M$, an injection $f : \{1, \dots, k\} \to I$, scalars $a_1, \dots, a_k$, and a basis $(n_j)$ of $N$ with $n_j = a_j e_{f(j)}$.

::: mathlib
`Module.Basis.SmithNormalForm` · `Mathlib.LinearAlgebra.FreeModule.PID`

The structure `Basis.SmithNormalForm N ι n`, with the fields `bM : Basis ι R M`, `bN : Basis (Fin n) R N`, `f : Fin n ↪ ι` and `a : Fin n → R`. It has no condition of divisibility on `a`. The divisible form is a theorem only over a Euclidean domain or for special cases.

<?decl Module.Basis.SmithNormalForm?>
:::

### Theorems and proofs

**Theorem (Smith normal form over $\mathbb{Z}$).** For each $m \times n$ matrix $A$ over $\mathbb{Z}$ there are invertible matrices $P$ and $Q$ over $\mathbb{Z}$ such that $P A Q$ is in Smith normal form.

*Proof.* The allowed operations are: swap two rows or two columns; multiply a row or a column by $-1$; add an integer multiple of a row to another row, or of a column to another column. Each is the product with an invertible matrix over $\mathbb{Z}$, on the left for the rows and on the right for the columns. Induction on $m + n$. If $A = 0$, it is in Smith normal form. Otherwise:

Step 1. Move an entry of the least nonzero absolute value to the position $(1, 1)$, and call it $a$.

Step 2. If an entry $b$ of the first column is not divisible by $a$, write $b = q a + r$ with $0 < r < |a|$, and subtract $q$ times the row $1$ from the row of $b$. The new entry $r$ is smaller than $|a|$: go back to Step 1. Do the same for the first row with column operations. Since $|a|$ decreases at each return, this terminates. Then $a$ divides each entry of the first row and column, and row and column operations make them $0$ except $a$.

Step 3. Now $A = \begin{pmatrix} a & 0 \\ 0 & A' \end{pmatrix}$. If an entry $b$ of $A'$ is not divisible by $a$, add its row to the row $1$. The first row now contains $b$, and Step 2 produces a smaller entry: go back to Step 1. This terminates for the same reason.

Step 4. Now $a$ divides each entry of $A'$. By the induction hypothesis, $P' A' Q' = \operatorname{diag}(d_2, \dots, d_k, 0, \dots)$ with $d_2 \mid d_3 \mid \dots$. The entries of $P' A' Q'$ are combinations of the entries of $A'$ with integer coefficients, so $a \mid d_2$. With $d_1 = a$, the matrix is in Smith normal form. $\square$

The same proof works over each Euclidean domain, with the Euclidean function in place of the absolute value. For $K[X]$ it uses the degree.

**Theorem (Invariants from the minors).** In the Smith normal form of $A$, the product $d_1 \cdots d_j$ is the greatest common divisor of the minors of size $j$ of $A$, up to a unit. So the $d_i$ are unique up to units.

The proof uses the formula of Cauchy and Binet for the minors of a product, and it is not given here. For a $2 \times 2$ matrix of rank $2$ the statement is: $d_1$ is the gcd of the four entries, and $d_1 d_2 = \pm \det A$.

**Theorem (Smith normal form of a submodule).** Let $R$ be a PID, $M$ free with a finite basis, and $N \subseteq M$ a submodule. Then $N$ has a Smith normal form.

Over $\mathbb{Z}$ this follows from the matrix form. By Section 1, $N$ has a basis $n_1, \dots, n_k$. Let $A$ be the matrix whose columns are the coordinates of the $n_j$ in a basis of $M$. A column operation on $A$ changes the basis of $N$, and a row operation changes the basis of $M$. So $P A Q = D$ in Smith normal form gives new bases of $M$ and $N$ with $n_j' = d_j e_j'$.

::: mathlib
`Submodule.smithNormalForm` · `Mathlib.LinearAlgebra.FreeModule.PID`

For a finite basis `b` of `M` over a PID and a submodule `N`: a pair of `n` and a `Basis.SmithNormalForm N ι n`. Mathlib proves it over each PID with an induction on the rank, which chooses a functional whose image of `N` is a maximal ideal among such images.

<?decl Submodule.smithNormalForm?>
:::

::: mathlib
`Ideal.exists_smith_normal_form` · `Mathlib.LinearAlgebra.FreeModule.PID`

The form for a nonzero ideal `I` of a ring `S` that is free of finite rank over `R`, such as the ring of integers of a number field over `ℤ`. Algebraic number theory uses it to compute the norm of an ideal.

<?decl Ideal.exists_smith_normal_form?>
:::

**Theorem (Structure theorem).** Let $M$ be a finitely generated module over a PID $R$. Then
$$M \cong R^r \oplus R/(d_1) \oplus \dots \oplus R/(d_k)$$
with nonzero nonunits $d_1 \mid \dots \mid d_k$. Also $M \cong R^r \oplus \bigoplus_i R/(p_i^{e_i})$ with primes $p_i$ and $e_i \ge 1$.

*Proof.* Let $x_1, \dots, x_n$ generate $M$, and let $\pi : R^n \to M$ send $e_i$ to $x_i$. Then $M \cong R^n / N$ with $N = \ker \pi$. By the Smith normal form, there is a basis $e_1', \dots, e_n'$ of $R^n$ with $N = R d_1 e_1' \oplus \dots \oplus R d_k e_k'$, with $k \le n$. So
$$M \cong R^n / N \cong R/(d_1) \oplus \dots \oplus R/(d_k) \oplus R^{n - k}.$$
The summands with $d_i$ a unit are $0$ and can be dropped. For the second form, factor each $d = u \prod_p p^{e_p}$. The ideals $(p^{e_p})$ for distinct primes are pairwise coprime, so the Chinese remainder theorem gives $R/(d) \cong \prod_p R/(p^{e_p})$. $\square$

The torsion submodule of $M$ is $\bigoplus R/(d_i)$, and $r$ is the rank of the free module $M / M_{\mathrm{tors}}$. For a torsion module, the summands $R/(p^e)$ for one prime $p$ form the $p$-primary component, the elements killed by a power of $p$.

::: mathlib
`Module.equiv_free_prod_directSum` · `Mathlib.Algebra.Module.PID`

The structure theorem in the primary form: for a finitely generated module over a PID, `∃ n ι _ p, (∀ i, Irreducible (p i)) ∧ ∃ e, Nonempty (M ≃ₗ[R] (Fin n →₀ R) × ⨁ i, R ⧸ R ∙ p i ^ e i)`. The free part is `Fin n →₀ R`, the finitely supported functions, which is `R^n`.

<?decl Module.equiv_free_prod_directSum?>
:::

::: mathlib
`Module.equiv_directSum_of_isTorsion` · `Mathlib.Algebra.Module.PID`

The torsion case: a finitely generated torsion module is `⨁ i, R ⧸ R ∙ p i ^ e i` with irreducible `p i`.

<?decl Module.equiv_directSum_of_isTorsion?>
:::

::: mathlib
`Submodule.isInternal_prime_power_torsion_of_pid` · `Mathlib.Algebra.Module.PID`

The primary decomposition: a finitely generated torsion module is the internal direct sum of its `p`-primary parts `torsionBy R M (p ^ e)`, over the prime factors `p` of its annihilator.

<?decl Submodule.isInternal_prime_power_torsion_of_pid?>
:::

::: mathlib
`Submodule.quotientEquivPiZMod` · `Mathlib.LinearAlgebra.FreeModule.Finite.Quotient`

For a subgroup `N` of `M ≅ ℤ^n` of full rank: `M ⧸ N ≃+ Π i, ZMod |a i|`, with the coefficients `a i` of the Smith normal form. It is the form used for explicit quotients of `ℤ^n`.

<?decl Submodule.quotientEquivPiZMod?>
:::

::: mathlib
`Submodule.quotientEquivDirectSum` · `Mathlib.LinearAlgebra.FreeModule.Finite.Quotient`

The same over a PID: `M ⧸ N` as a direct sum of the quotients `R ⧸ span {a i}`, for `N` of full rank.

<?decl Submodule.quotientEquivDirectSum?>
:::

::: mathlib
`AddSubgroup.index_eq_natAbs_det` · `Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient`

The index of a subgroup `N` of `E ≅ ℤ^n` with a basis `bN` of the same size is `|det|` of the matrix of `bN` in a basis of `E`.

<?decl AddSubgroup.index_eq_natAbs_det?>
:::

### Examples

**Example (The quotient $\mathbb{Z}^2 / \langle (2, 4), (6, 8) \rangle$).** Let $N$ be generated by $(2, 4)$ and $(6, 8)$. Write the generators as the rows of $A = \begin{pmatrix} 2 & 4 \\ 6 & 8 \end{pmatrix}$; with the rows, a row operation changes the generators of $N$ and a column operation changes the basis of $\mathbb{Z}^2$. Subtract $3$ times the row $1$ from the row $2$: $\begin{pmatrix} 2 & 4 \\ 0 & -4 \end{pmatrix}$. Subtract $2$ times the column $1$ from the column $2$: $\begin{pmatrix} 2 & 0 \\ 0 & -4 \end{pmatrix}$. Multiply the row $2$ by $-1$: $D = \operatorname{diag}(2, 4)$, and $2 \mid 4$.

The column operation corresponds to the new coordinates $(x, y - 2x)$, that is, to the basis $f_1 = (1, 2)$, $f_2 = (0, 1)$ of $\mathbb{Z}^2$: $(x, y) = x f_1 + (y - 2x) f_2$. In this basis, $(2, 4) = 2 f_1$ and $(6, 8) - 3(2, 4) = (0, -4) = -4 f_2$. So $N = 2\mathbb{Z} f_1 \oplus 4\mathbb{Z} f_2$, and
$$\mathbb{Z}^2 / N \cong \mathbb{Z}/2 \oplus \mathbb{Z}/4.$$
The invariants agree with the minors: the gcd of the entries $2, 4, 6, 8$ is $2 = d_1$, and $|\det A| = |16 - 24| = 8 = d_1 d_2$. The order of the quotient is $8$, the index of $N$. The quotient is not cyclic: each element is killed by $4$, so no element has the order $8$.

**Example (Abelian groups of order $8$).** By the structure theorem, a finite abelian group of order $8$ is one of $\mathbb{Z}/8$, $\mathbb{Z}/2 \oplus \mathbb{Z}/4$, $\mathbb{Z}/2 \oplus \mathbb{Z}/2 \oplus \mathbb{Z}/2$. They correspond to the partitions $3$, $2 + 1$, $1 + 1 + 1$ of the exponent. They are pairwise not isomorphic: the numbers of the elements of order at most $2$ are $2$, $4$ and $8$.

**Example (Two forms of one group).** Let $G = \mathbb{Z}/12 \oplus \mathbb{Z}/18$. The primary form: $12 = 4 \cdot 3$ and $18 = 2 \cdot 9$, so $G \cong \mathbb{Z}/4 \oplus \mathbb{Z}/3 \oplus \mathbb{Z}/2 \oplus \mathbb{Z}/9$. For the invariant factors, collect the highest powers of each prime first: $d_2 = 4 \cdot 9 = 36$, then $d_1 = 2 \cdot 3 = 6$. So $G \cong \mathbb{Z}/6 \oplus \mathbb{Z}/36$, with $6 \mid 36$ and $6 \cdot 36 = 216 = 12 \cdot 18$. The Smith form of $\operatorname{diag}(12, 18)$ gives the same result: the gcd of the entries is $6$, and the determinant is $216$.

**Example (A module over $\mathbb{Q}[X]$).** Let $A = \operatorname{diag}(2, 2, 3)$ act on $\mathbb{Q}^3$, as in Chapter 5. The Smith form of $X I - A = \operatorname{diag}(X - 2, X - 2, X - 3)$ over $\mathbb{Q}[X]$: the gcd of the entries is $1$, the gcd of the minors of size $2$ is $X - 2$, and the determinant is $(X - 2)^2 (X - 3)$. So the invariant factors are $1$, $X - 2$ and $(X - 2)(X - 3)$, and the module is $\mathbb{Q}[X]/(X - 2) \oplus \mathbb{Q}[X]/((X - 2)(X - 3))$. The last invariant factor is the minimal polynomial of $A$, and the product is $\chi_A$.

**Counterexample (Outside a PID).** Over $\mathbb{Z}[X]$, the module $\mathbb{Z}[X]/(2, X) \cong \mathbb{Z}/2$ is killed by the ideal $(2, X)$, which is not principal. It is not of the form $\mathbb{Z}[X]/(d)$ for an element $d$: the annihilator of $\mathbb{Z}[X]/(d)$ is $(d)$, a principal ideal, and the annihilator of $\mathbb{Z}/2$ is $(2, X)$. A direct sum of several modules $\mathbb{Z}[X]/(d_i)$ is also excluded: $\mathbb{Z}/2$ has two elements, so only one summand could be nonzero.

### The library around it

The structure theorem is in `Mathlib.Algebra.Module.PID`, and the Smith normal form of a submodule in `Mathlib.LinearAlgebra.FreeModule.PID`. The quotients of free modules of full rank are in `Mathlib.LinearAlgebra.FreeModule.Finite.Quotient`, and the index formula in `Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient`. The finite abelian groups have their own form, `AddCommGroup.equiv_directSum_zmod_of_finite`, in `Mathlib.GroupTheory.FiniteAbelian.Basic`.

### Exercises

1. (A) Compute $\mathbb{Z}^2 / \langle (4, 6), (2, 2) \rangle$ by the Smith normal form.
2. (A) Compute $\mathbb{Z}^3 / \langle (1, 1, 1), (0, 2, 2), (0, 0, 3) \rangle$.
3. (A) List the abelian groups of order $36$, in both forms.
4. (B) Show that $\mathbb{Z}/m \oplus \mathbb{Z}/n \cong \mathbb{Z}/\gcd(m, n) \oplus \mathbb{Z}/\operatorname{lcm}(m, n)$. Hint: the Smith normal form of $\operatorname{diag}(m, n)$.
5. (B) Show that a finitely generated abelian group $G$ with $G \otimes \mathbb{Q} = 0$ is finite. Hint: $r = 0$ in the structure theorem.
6. (B) Find the invariant factors of the $\mathbb{Q}[X]$-module defined by $\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$, and compare with Section 1.
7. (C) Let $A$ be an $n \times n$ matrix over a field $K$. Show that the last invariant factor of $X I - A$ is the minimal polynomial of $A$, and that the product of the invariant factors is $\chi_A$. Deduce the theorem of Cayley and Hamilton again.

### Notes and history

Smith introduced the normal form of integer matrices in 1861, in a study of systems of linear equations over the integers. Frobenius and Stickelberger proved the classification of the finite abelian groups in 1879, after an earlier proof by Kronecker in 1870. The form over a PID and the application to the normal forms of matrices over $K[X]$ became standard with van der Waerden's Moderne Algebra in 1930 and 1931.

### Reference

<?reference?>
