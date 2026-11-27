---
title: Lie rings, Lie algebras and Lie modules
kind: theory
modules:
  - Mathlib.Algebra.Lie.Basic
  - Mathlib.Algebra.Lie.OfAssociative
  - Mathlib.Algebra.Lie.Abelian
  - Mathlib.Algebra.Lie.Matrix
  - Mathlib.Algebra.Lie.Classical
  - Mathlib.Algebra.Lie.SkewAdjoint
  - Mathlib.Algebra.Lie.NonUnitalNonAssocAlgebra
explains:
  E3: [LieRing, LieAlgebra, LieRingModule, LieModule, lie_skew, lie_jacobi, LieRing.ofAssociativeRing, LieModule.toEnd, LieAlgebra.ad, LieAlgebra.SpecialLinear.sl, LieAlgebra.matrix_trace_commutator_zero, LieAlgebra.SpecialLinear.sl_non_abelian, LieAlgebra.Orthogonal.mem_so, LieAlgebra.Symplectic.sp, skewAdjointMatricesLieSubalgebra, LinearMap.BilinForm.isSkewAdjoint_bracket, IsLieAbelian]
  E2: [LieHom, LieEquiv, LieModuleHom, LieModuleEquiv, lie_self, leibniz_lie, lie_lie, LieRing.of_associative_ring_bracket, LieAlgebra.ofAssociativeAlgebra, AlgHom.toLieHom, LieModule.IsFaithful, LieAlgebra.ad_apply, LieRingModule.toEnd, lieEquivMatrix', Matrix.lieConj, Matrix.reindexLieEquiv, LieAlgebra.Orthogonal.so, LieAlgebra.Orthogonal.so', LieAlgebra.Orthogonal.typeB, LieAlgebra.Orthogonal.typeD, LieAlgebra.Orthogonal.soIndefiniteEquiv, LieAlgebra.SpecialLinear.single, LieAlgebra.SpecialLinear.singleSubSingle, skewAdjointLieSubalgebra, Matrix.lie_transpose, LieModule.IsTrivial, LieAlgebra.center, LieModule.ker, LieModule.maxTrivSubmodule, TrivialLieModule, CommutatorRing, LieHom.toNonUnitalAlgHom, LieRing.toNonUnitalNonAssocRing]
  E1: auto
families: []
requires: [V06.C08, V07.C01, V07.C03, V08.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lie rings, Lie algebras and Lie modules

### Overview

A Lie algebra is a vector space with a bilinear product, the bracket $[x, y]$, that is alternating and satisfies the Jacobi identity. The first source of Lie algebras is the commutator $[a, b] = ab - ba$ in an associative algebra, and the Jacobi identity is what remains of associativity. Lie found these structures as the infinitesimal form of continuous groups: the tangent space at the identity of a Lie group carries a bracket, and the bracket determines the group near the identity.

This section gives the axioms in the form of Mathlib, which separates the additive part (`LieRing`) from the scalars (`LieAlgebra`), and defines Lie modules, the adjoint representation, abelian Lie algebras and trivial modules, and it builds the classical Lie algebras $\mathfrak{gl}(n)$, $\mathfrak{sl}(n)$, $\mathfrak{so}(n)$ and $\mathfrak{sp}(2n)$ as Lie subalgebras of square matrices. The running example is $\mathfrak{sl}_2$ with its basis $e, f, h$. Mathlib writes the bracket as `⁅x, y⁆`, with the white square brackets, to keep `[x, y]` free for lists.

### Definitions

**Definition (Lie ring).** A Lie ring is an abelian group $L$ with a map $L \times L \to L$, $(x, y) \mapsto [x, y]$, that is additive in each variable, satisfies $[x, x] = 0$ for all $x$, and satisfies the Leibniz rule $$[x, [y, z]] = [[x, y], z] + [y, [x, z]].$$

The Leibniz rule says that $\operatorname{ad} x = [x, -]$ is a derivation of the bracket. It is the Jacobi identity in another form, and it extends without change to modules.

**Definition (Lie algebra).** Let $R$ be a commutative ring. A Lie algebra over $R$ is a Lie ring $L$ that is also an $R$-module, such that $[x, t y] = t [x, y]$ for all $t \in R$ and $x, y \in L$.

Linearity in the first variable follows from $[x, y] = -[y, x]$, so the class asks only for the second.

**Definition (Lie module).** Let $L$ be a Lie ring. A Lie ring module over $L$ is an abelian group $M$ with a map $L \times M \to M$, $(x, m) \mapsto [x, m]$, additive in each variable, with $$[x, [y, m]] = [[x, y], m] + [y, [x, m]].$$ If $L$ is a Lie algebra over $R$ and $M$ is an $R$-module, $M$ is a Lie module if in addition $[t x, m] = t [x, m]$ and $[x, t m] = t [x, m]$.

A Lie module is the same as a representation $\rho \colon L \to \operatorname{End}_R(M)$ with $\rho([x, y]) = \rho(x)\rho(y) - \rho(y)\rho(x)$; the axiom is this identity applied to $m$.

**Definition (Morphisms).** A morphism of Lie algebras $f \colon L \to L'$ is an $R$-linear map with $f([x, y]) = [f(x), f(y)]$. A morphism of Lie modules $g \colon M \to N$ over $L$ is an $R$-linear map with $g([x, m]) = [x, g(m)]$. An equivalence is a bijective morphism.

**Definition (Commutator algebra).** Let $A$ be an associative algebra over $R$. The commutator Lie algebra of $A$ is the $R$-module $A$ with the bracket $[a, b] = ab - ba$. For $A = \operatorname{End}_R(V)$ it is written $\mathfrak{gl}(V)$, and for $A = M_n(R)$ it is written $\mathfrak{gl}_n(R)$.

**Definition (Adjoint representation).** The adjoint representation of a Lie algebra $L$ is the Lie module $L$ over itself, with $\operatorname{ad} x(y) = [x, y]$.

**Definition (Abelian, trivial, center).** A Lie algebra is abelian if $[x, y] = 0$ for all $x, y$. A Lie module $M$ is trivial if $[x, m] = 0$ for all $x \in L$ and $m \in M$. The center of $L$ is $Z(L) = \{z \in L : [x, z] = 0 \text{ for all } x\}$. The kernel of a Lie module $M$ is the ideal of the $x$ with $[x, m] = 0$ for all $m$, and $M$ is faithful if the kernel is $0$.

**Definition (Classical Lie algebras).** Let $n \geq 1$. The special linear Lie algebra is $\mathfrak{sl}_n(R) = \{A \in M_n(R) : \operatorname{tr} A = 0\}$. For a matrix $J \in M_n(R)$, the Lie algebra of $J$-skew-adjoint matrices is $\{A : A^{T} J + J A = 0\}$. The orthogonal Lie algebra $\mathfrak{so}_n(R)$ is the case $J = I$, that is $A^{T} = -A$. The symplectic Lie algebra $\mathfrak{sp}_{2l}(R)$ is the case $$J = \begin{pmatrix} 0 & -I_l \\ I_l & 0 \end{pmatrix}.$$

### Theorems and proofs

**Proposition (Anticommutativity).** In a Lie ring, $[x, y] = -[y, x]$ for all $x, y$.

*Proof.* Expand $[x + y, x + y] = 0$ by additivity in each variable: $[x, x] + [x, y] + [y, x] + [y, y] = 0$. The first and the last terms are $0$. So $[x, y] + [y, x] = 0$. $\square$

The converse fails in characteristic $2$, so Mathlib takes $[x, x] = 0$ as the axiom.

**Proposition (Jacobi identity).** In a Lie ring, $[x, [y, z]] + [y, [z, x]] + [z, [x, y]] = 0$.

*Proof.* By the Leibniz rule, $[x, [y, z]] = [[x, y], z] + [y, [x, z]]$. By anticommutativity, $[[x, y], z] = -[z, [x, y]]$ and $[y, [x, z]] = -[y, [z, x]]$. Substitute and move the terms to one side. $\square$

**Theorem (The commutator bracket).** Let $A$ be an associative ring. Then $[a, b] = ab - ba$ makes $A$ a Lie ring. If $A$ is an algebra over $R$, it is a Lie algebra over $R$, and a morphism of $R$-algebras $A \to B$ is a morphism of Lie algebras.

*Proof.* The bracket is additive in each variable by the two distributive laws, and $[a, a] = a^2 - a^2 = 0$. For the Leibniz rule, expand both sides with the associative law: $$[a, [b, c]] = abc - acb - bca + cba,$$ $$[[a, b], c] + [b, [a, c]] = (abc - bac - cab + cba) + (bac - bca - acb + cab).$$ The terms $bac$ and $cab$ cancel on the right, and the two sides agree. For an algebra, $[a, t b] = a (t b) - (t b) a = t(ab - ba)$, because scalars commute with all elements. An algebra morphism $f$ satisfies $f(ab - ba) = f(a) f(b) - f(b) f(a)$. $\square$

**Theorem (A Lie module is a representation).** Let $M$ be a Lie module over $L$. The map $\rho \colon L \to \mathfrak{gl}(M)$, $\rho(x)(m) = [x, m]$, is a morphism of Lie algebras. In particular $\operatorname{ad} \colon L \to \mathfrak{gl}(L)$ is a morphism of Lie algebras, and its kernel is the center $Z(L)$.

*Proof.* Each $\rho(x)$ is $R$-linear by the two axioms on $[x, -]$, and $\rho$ is $R$-linear by the two axioms on $[-, m]$. For $m \in M$, the module axiom gives $[[x, y], m] = [x, [y, m]] - [y, [x, m]]$, that is $\rho([x, y])(m) = (\rho(x)\rho(y) - \rho(y)\rho(x))(m)$. So $\rho([x, y]) = [\rho(x), \rho(y)]$ in $\mathfrak{gl}(M)$. For $M = L$, $\operatorname{ad} x = 0$ means $[x, y] = 0$ for all $y$, which is $x \in Z(L)$ by anticommutativity. $\square$

**Proposition (The trace of a commutator).** For $X, Y \in M_n(R)$, $\operatorname{tr}[X, Y] = 0$. So $\mathfrak{sl}_n(R)$ is a Lie subalgebra of $\mathfrak{gl}_n(R)$, and $[\mathfrak{gl}_n(R), \mathfrak{gl}_n(R)] \subseteq \mathfrak{sl}_n(R)$.

*Proof.* $\operatorname{tr}(XY) = \sum_{i, j} X_{ij} Y_{ji} = \sum_{j, i} Y_{ji} X_{ij} = \operatorname{tr}(YX)$, because $R$ is commutative. So $\operatorname{tr}(XY - YX) = 0$. The trace is linear, so $\mathfrak{sl}_n(R)$ is a submodule, and it is closed under the bracket by the first statement. $\square$

**Proposition (Skew-adjoint matrices).** Let $J \in M_n(R)$. The $J$-skew-adjoint matrices form a Lie subalgebra of $\mathfrak{gl}_n(R)$. The same holds for the endomorphisms that are skew-adjoint for a bilinear form $B$ on a module $M$, that is the $f$ with $B(f u, v) = -B(u, f v)$.

*Proof.* Work with the form $B$; the matrix case is the form $B(u, v) = u^T J v$. The condition is linear in $f$, so the skew-adjoint maps form a submodule. Let $f$ and $g$ be skew-adjoint. Then $$B(fg u, v) = -B(g u, f v) = B(u, g f v),$$ and in the same way $B(gf u, v) = B(u, fg v)$. Subtract: $B([f, g] u, v) = B(u, (gf - fg) v) = -B(u, [f, g] v)$. $\square$

**Proposition (Non-abelian).** If $R$ is a nonzero ring and $n \geq 2$, then $\mathfrak{sl}_n(R)$ is not abelian.

*Proof.* Choose $i \neq j$, and let $E_{ij}$ be the matrix unit. Both $E_{ij}$ and $E_{ji}$ have trace $0$. Their bracket is $E_{ij}E_{ji} - E_{ji}E_{ij} = E_{ii} - E_{jj}$, which is not $0$ because its entry at $(i, i)$ is $1 \neq 0$. $\square$

**Proposition (Dimensions).** Over a field of characteristic not $2$, $\dim \mathfrak{sl}_n = n^2 - 1$, $\dim \mathfrak{so}_n = n(n-1)/2$ and $\dim \mathfrak{sp}_{2l} = l(2l + 1)$.

*Proof.* The trace is a nonzero linear form on $M_n$, so its kernel has dimension $n^2 - 1$. A matrix with $A^T = -A$ has zero diagonal (because $2 A_{ii} = 0$ and $2$ is invertible) and is determined by the $n(n-1)/2$ entries above the diagonal. For $\mathfrak{sp}_{2l}$, write $A$ in blocks $\begin{pmatrix} a & b \\ c & d \end{pmatrix}$. A computation with the block form of $J$ shows that $A^T J + J A = 0$ holds if and only if $d = -a^T$, $b = b^T$ and $c = c^T$. So $a$ is free ($l^2$ parameters), and $b$ and $c$ are symmetric ($l(l+1)/2$ parameters each). The total is $l^2 + l(l+1) = l(2l+1)$. $\square$

### Examples

**Example (The bracket table of $\mathfrak{sl}_2$).** The Lie algebra $\mathfrak{sl}_2(R)$ has the basis $$e = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}, \quad f = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}, \quad h = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}.$$ The products are $ef = \operatorname{diag}(1, 0)$ and $fe = \operatorname{diag}(0, 1)$, so $[e, f] = h$. Next $he = e$ and $eh = -e$, so $[h, e] = 2e$. Last $hf = -f$ and $fh = f$, so $[h, f] = -2f$. With anticommutativity, the three relations $$[h, e] = 2e, \qquad [h, f] = -2f, \qquad [e, f] = h$$ determine the bracket. In the ordered basis $(e, h, f)$, the adjoint matrices are $$\operatorname{ad} h = \begin{pmatrix} 2 & 0 & 0 \\ 0 & 0 & 0 \\ 0 & 0 & -2 \end{pmatrix}, \quad \operatorname{ad} e = \begin{pmatrix} 0 & -2 & 0 \\ 0 & 0 & 1 \\ 0 & 0 & 0 \end{pmatrix}, \quad \operatorname{ad} f = \begin{pmatrix} 0 & 0 & 0 \\ -1 & 0 & 0 \\ 0 & 2 & 0 \end{pmatrix}.$$ The matrix $\operatorname{ad} h$ is diagonal with eigenvalues $2, 0, -2$. This is the first case of the root decomposition of Chapter 6.

**Example (The cross product).** The orthogonal Lie algebra $\mathfrak{so}_3(\mathbb{R})$ has the basis $$L_1 = \begin{pmatrix} 0 & 0 & 0 \\ 0 & 0 & -1 \\ 0 & 1 & 0 \end{pmatrix}, \quad L_2 = \begin{pmatrix} 0 & 0 & 1 \\ 0 & 0 & 0 \\ -1 & 0 & 0 \end{pmatrix}, \quad L_3 = \begin{pmatrix} 0 & -1 & 0 \\ 1 & 0 & 0 \\ 0 & 0 & 0 \end{pmatrix}.$$ A direct multiplication gives $L_1 L_2 = E_{21}$ and $L_2 L_1 = E_{12}$, so $[L_1, L_2] = E_{21} - E_{12} = L_3$. In the same way $[L_2, L_3] = L_1$ and $[L_3, L_1] = L_2$. The map $L_i \mapsto e_i$ is an equivalence of $\mathfrak{so}_3(\mathbb{R})$ with $\mathbb{R}^3$ and the cross product, because $e_1 \times e_2 = e_3$ and the other products follow cyclically.

**Example (An abelian Lie algebra and a trivial module).** Each $R$-module is an abelian Lie algebra with the bracket $0$. A one-dimensional Lie algebra is abelian, because $[t x, s x] = ts [x, x] = 0$. The trivial module $R$ over any $L$ has $[x, t] = 0$. The center of $\mathfrak{gl}_n(K)$ over a field $K$ is the line of scalar matrices: a matrix that commutes with all $E_{ij}$ is scalar. The center of $\mathfrak{sl}_2(K)$ is $0$ when the characteristic of $K$ is not $2$:  if $z = a e + b h + c f$ is central, then $[h, z] = 2ae - 2cf = 0$ gives $a = c = 0$, and $[e, z] = -2b e = 0$ gives $b = 0$. In characteristic $2$ the matrix $h$ equals $I$ and is central, so the later theorems on semisimplicity need characteristic $0$.

### The library around it

::: mathlib
`LieRing` · `Mathlib.Algebra.Lie.Basic`

The class `LieRing L` extends `AddCommGroup L` and `Bracket L L` with the fields `add_lie`, `lie_add`, `lie_self` and `leibniz_lie`, in the form of the text. `LieAlgebra R L` extends `Module R L` with the single field `lie_smul`. The derived facts are `lie_skew : -⁅y, x⁆ = ⁅x, y⁆`, `lie_jacobi` and `lie_lie`, the form $[[x, y], m] = [x, [y, m]] - [y, [x, m]]$. Morphisms are `L →ₗ⁅R⁆ L'` (`LieHom`), equivalences are `L ≃ₗ⁅R⁆ L'` (`LieEquiv`), and the module versions are `M →ₗ⁅R,L⁆ N` (`LieModuleHom`) and `LieModuleEquiv`.

<?decl LieRing?>
:::

::: mathlib
`LieModule` · `Mathlib.Algebra.Lie.Basic`

A Lie module needs two classes. `LieRingModule L M` gives the bracket `⁅x, m⁆` with additivity and the Leibniz rule, and needs no scalars. `LieModule R L M` is a `Prop` with the two fields `smul_lie` and `lie_smul`. The representation itself is `LieModule.toEnd R L M : L →ₗ⁅R⁆ Module.End R M`, and `LieAlgebra.ad R L` is the case `M = L`, with `LieAlgebra.ad_apply : ad R L x y = ⁅x, y⁆`. `LieModule.IsFaithful R L M` says that `toEnd` is injective.

<?decl LieModule?>
:::

::: mathlib
`LieRing.ofAssociativeRing` · `Mathlib.Algebra.Lie.OfAssociative`

The bracket `⁅a, b⁆ = a * b - b * a` on any ring is a global instance in `Mathlib.Algebra.Ring.Commute`, with `Ring.lie_def`. The Lie ring structure on a ring is the definition `LieRing.ofAssociativeRing`, not a global instance, and the files of the library switch it on with `attribute [local instance 100] LieRing.ofAssociativeRing`. Its bracket lemma is `LieRing.of_associative_ring_bracket`. On top of it, the instance `LieAlgebra.ofAssociativeAlgebra` gives the Lie algebra over `R`, and `AlgHom.toLieHom` turns an algebra morphism into a Lie morphism. `lieEquivMatrix'` identifies `Module.End R (n → R)` with `Matrix n n R`, and `Matrix.lieConj` and `Matrix.reindexLieEquiv` conjugate and reindex.

<?decl LieRing.ofAssociativeRing?>
:::

::: mathlib
`LieAlgebra.SpecialLinear.sl` · `Mathlib.Algebra.Lie.Classical`

`sl n R : LieSubalgebra R (Matrix n n R)` is the kernel of the trace, made a subalgebra with `matrix_trace_commutator_zero n R X Y : trace ⁅X, Y⁆ = 0`. The basis elements are `single i j h r`, the matrix $r E_{ij}$ for `h : i ≠ j`, and `singleSubSingle i j r`, the matrix $r(E_{ii} - E_{jj})$. `sl_non_abelian` states `¬IsLieAbelian (sl n R)` when `1 < Fintype.card n` and `R` is nontrivial, with the proof of the text. `Symplectic.sp l R` lives in `Matrix (l ⊕ l) (l ⊕ l) R` and uses `Matrix.J l R = fromBlocks 0 (-1) 1 0`, `Orthogonal.so n R` has `mem_so : A ∈ so n R ↔ Aᵀ = -A`, and `so'`, `typeB`, `typeD` use other forms, for which the diagonal matrices form a Cartan subalgebra; `soIndefiniteEquiv` compares two of them when $-1$ is a square.

<?decl LieAlgebra.SpecialLinear.sl?>
:::

::: mathlib
`skewAdjointMatricesLieSubalgebra` · `Mathlib.Algebra.Lie.SkewAdjoint`

`skewAdjointMatricesLieSubalgebra J` is the Lie subalgebra of the `J`-skew-adjoint matrices, and `mem_skewAdjointMatricesLieSubalgebra` reduces membership to the submodule `skewAdjointMatricesSubmodule J`. For a bilinear form `B`, `skewAdjointLieSubalgebra B` is the version for endomorphisms, and `LinearMap.BilinForm.isSkewAdjoint_bracket` is the closure under the bracket proved in the text. `Matrix.lie_transpose` states $[A, B]^T = [B^T, A^T]$.

<?decl skewAdjointMatricesLieSubalgebra?>
:::

::: mathlib
`IsLieAbelian` · `Mathlib.Algebra.Lie.Abelian`

`IsLieAbelian L` is an abbreviation for `LieModule.IsTrivial L L`, and `LieModule.IsTrivial L M` has the single field `trivial : ∀ x m, ⁅x, m⁆ = 0`. The center `LieAlgebra.center R L` is a Lie ideal, `LieModule.ker R L M` is the kernel of the representation, and `LieModule.maxTrivSubmodule R L M` is the largest trivial submodule, the invariants $M^L$. `TrivialLieModule R L M` is a type synonym of `M` with the zero action. In `Mathlib.Algebra.Lie.NonUnitalNonAssocAlgebra`, the type synonym `CommutatorRing L` turns the bracket into a multiplication, with `LieRing.toNonUnitalNonAssocRing`, and `LieHom.toNonUnitalAlgHom` sends Lie morphisms to morphisms of non-unital non-associative algebras.

<?decl IsLieAbelian?>
:::

Common errors of a learner: The first error is to write `[x, y]` for the bracket; Lean reads it as a list, and the bracket is `⁅x, y⁆`, typed `\[-` and `\-]`. The second error is to expect a Lie structure on `Matrix n n R` without a local instance; the bracket exists globally, but lemmas that need `LieRing` on a ring need `LieRing.ofAssociativeRing` as a local instance. The third error is to state a representation with `LieModule R L M` alone; the class needs `LieRingModule L M` first. The fourth error is to forget that `sp l R` is indexed by `l ⊕ l`, so $\mathfrak{sp}_4$ is `sp (Fin 2) R`.

### Exercises

1. (A) Write out the bracket table of $\mathfrak{gl}_2(R)$ in the basis $E_{11}, E_{12}, E_{21}, E_{22}$, and show that $\mathfrak{gl}_2 = \mathfrak{sl}_2 \oplus R \cdot I$ as Lie algebras when $2$ is invertible in $R$. Hint: $[E_{ij}, E_{kl}] = \delta_{jk} E_{il} - \delta_{li} E_{kj}$.
2. (A) Show that the two-dimensional Lie algebra with basis $x, y$ and $[x, y] = y$ is not abelian and has center $0$. Hint: compute $[a x + b y, x]$ and $[a x + b y, y]$.
3. (A) Show that the matrices of $\operatorname{ad} e$, $\operatorname{ad} f$, $\operatorname{ad} h$ in the example satisfy the bracket relations of $\mathfrak{sl}_2$, for example $[\operatorname{ad} e, \operatorname{ad} f] = \operatorname{ad} h$. Hint: this is the theorem that $\operatorname{ad}$ is a morphism; check one product of $3 \times 3$ matrices.
4. (B) Prove the block description of $\mathfrak{sp}_{2l}$ used in the proof of the dimensions, and find a basis of $\mathfrak{sp}_2$. Show that $\mathfrak{sp}_2 = \mathfrak{sl}_2$. Hint: for $l = 1$, $b$ and $c$ are scalars and $d = -a$.
5. (B) Let $D$ be the space of derivations of an $R$-algebra $A$, the linear maps with $D(ab) = D(a) b + a D(b)$. Show that $[D_1, D_2] = D_1 D_2 - D_2 D_1$ is again a derivation. Hint: expand $D_1 D_2(ab)$ and note that the mixed terms cancel in the commutator.
6. (C) Over a field of characteristic not $2$, find all Lie algebra structures on a two-dimensional vector space up to equivalence. Hint: the image of the bracket is spanned by $[x, y]$; if it is nonzero, choose $y$ in it and rescale $x$.

### Notes and history

Lie developed the theory of continuous transformation groups in the 1870s and 1880s, and the infinitesimal transformations of a group, with their commutators, were his main tool. Killing and Cartan classified the simple Lie algebras over the complex numbers, and the classical algebras $\mathfrak{sl}$, $\mathfrak{so}$ and $\mathfrak{sp}$ are the four infinite families $A_l$, $B_l$, $C_l$, $D_l$ of that classification. The name Lie algebra came later, in the work of Weyl.

The Mathlib files are by these authors, read from their headers: `Basic`, `OfAssociative`, `Abelian`, `Matrix`, `Classical`, `SkewAdjoint` and `NonUnitalNonAssocAlgebra` (all under `Mathlib.Algebra.Lie`) by Oliver Nash.

### Reference

<?reference?>
