---
title: Subspaces and the action of the linear group
kind: theory
modules:
  - Mathlib.LinearAlgebra.Projectivization.Subspace
  - Mathlib.LinearAlgebra.Projectivization.Action
  - Mathlib.LinearAlgebra.Projectivization.Collinear
  - Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
  - Mathlib.LinearAlgebra.Projectivization.Constructions
  - Mathlib.LinearAlgebra.Projectivization.PSL.Stabilizer
explains:
  E3: [Projectivization.Subspace, Projectivization.Subspace.span, Projectivization.smul_mk]
  E2: [Projectivization.Subspace.submodule, Submodule.projectivization, Projectivization.Subspace.mem_add, Projectivization.Subspace.mem_span, Projectivization.Subspace.span_le_subspace_iff, Projectivization.IsCollinear, Projectivization.line_unique, Projectivization.cross, Projectivization.cross_mk, Projectivization.mk_eq_mk_iff_crossProduct_eq_zero, Projectivization.orthogonal_mk, Projectivization.SL_mulAction_ker, Projectivization.PGL.mk_smul_mk, Matrix.ProjectiveSpecialLinearGroup.rank_two_simple]
  E1: auto
families: []
requires: [V07.C02, V07.C03, V05.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Subspaces and the action of the linear group

### Overview

A projective space has lines, planes and higher subspaces, and a group of symmetries. Both come from linear algebra: a projective subspace is the set of points of a linear subspace of $V$, and an invertible linear map permutes the lines through the origin.

It matches projective subspaces with submodules, proves the incidence of points and lines, computes lines of $\mathbb{P}^2$ by the cross product, and studies the action of $\mathrm{GL}(V)$ and the simplicity of $\mathrm{PSL}_2(F)$.

### Definitions

Let $K$ be a division ring and $V$ a $K$-vector space.

**Definition (Projective subspace).** A subspace of $\mathbb{P}(V)$ is a set $T$ of points such that, whenever $[v] \in T$, $[w] \in T$ and $v + w \neq 0$, also $[v + w] \in T$.

::: mathlib
`Projectivization.Subspace` · `Mathlib.LinearAlgebra.Projectivization.Subspace`

A carrier set of points and the field `mem_add'` for the closure condition. Subspaces form a complete lattice under inclusion.

<?decl Projectivization.Subspace?>
:::

<?decl Projectivization.Subspace.mem_add?>

**Definition (Span).** The span of a set $S$ of points is the intersection of all subspaces that contain $S$. It is the smallest subspace containing $S$.

::: mathlib
`Projectivization.Subspace.span` · `Mathlib.LinearAlgebra.Projectivization.Subspace`

Defined inductively as the closure of $S$ under the rule of `mem_add`; `mem_span` proves that it is the intersection of all subspaces containing $S$.

<?decl Projectivization.Subspace.span?>
:::

<?decl Projectivization.Subspace.mem_span?>

<?decl Projectivization.Subspace.span_le_subspace_iff?>

**Definition (Lines, planes, collinear points).** The dimension of a subspace is $\dim W - 1$ for its submodule $W$ (theorem below). Lines and planes have dimension $1$ and $2$, and a set of points is collinear if it lies in a line.

::: mathlib
`Projectivization.IsCollinear` · `Mathlib.LinearAlgebra.Projectivization.Collinear`

`IsCollinear S` asks for a subspace $M$ containing $S$ whose submodule is finite-dimensional of rank at most $2$.

<?decl Projectivization.IsCollinear?>
:::

**Definition (Projective linear group).** A group $G$ acting linearly on $V$, such as $\mathrm{GL}(V)$, acts on $\mathbb{P}(V)$ by $g \cdot [v] = [g v]$. For a field $K$, $\mathrm{PGL}_n(K) = \mathrm{GL}_n(K) / K^{\times}$, and $\mathrm{PSL}_n(K)$ is $\mathrm{SL}_n(K)$ modulo its center.

::: mathlib
`Projectivization.smul_mk` · `Mathlib.LinearAlgebra.Projectivization.Action`

The action exists for any group acting distributively on $V$ and commuting with $K$, and $g \cdot [v] = [g \cdot v]$. `PGL.mk_smul_mk` is the same rule for `Matrix.ProjGenLinGroup`.

<?decl Projectivization.smul_mk?>
:::

<?decl Projectivization.PGL.mk_smul_mk?>

### Theorems and proofs

**Theorem (Subspaces and submodules).** The map $W \mapsto \mathbb{P}(W) = \{[v] : v \in W, v \neq 0\}$ is an order isomorphism from the lattice of submodules of $V$ to the lattice of subspaces of $\mathbb{P}(V)$. Its inverse sends $T$ to $\{0\} \cup \{v \neq 0 : [v] \in T\}$.

*Proof.* If $W$ is a submodule and $[v], [w] \in \mathbb{P}(W)$, then $v, w \in W$, so $v + w \in W$ and $[v + w] \in \mathbb{P}(W)$ when $v + w \neq 0$. So $\mathbb{P}(W)$ is a subspace. Conversely, let $T$ be a subspace and $\widehat{T} = \{0\} \cup \{v \neq 0 : [v] \in T\}$. It is closed under scalars, since $a v$ is $0$ or represents $[v]$, and under addition, since for nonzero $v, w$ either $v + w = 0$ or $[v + w] \in T$. So $\widehat{T}$ is a submodule. The maps are inverse and monotone because $[v] \in \mathbb{P}(W)$ if and only if $v \in W$. $\square$

::: mathlib
`Projectivization.Subspace.submodule` · `Mathlib.LinearAlgebra.Projectivization.Subspace`

The order isomorphism from subspaces to submodules; its inverse is `Submodule.projectivization`.

<?decl Projectivization.Subspace.submodule?>
:::

<?decl Submodule.projectivization?>

**Theorem (Two points determine a line).** Let $x \neq y$ be points of $\mathbb{P}(V)$. There is exactly one line containing both.

*Proof.* Write $x = [v]$ and $y = [w]$. Since $x \neq y$, the vectors $v$ and $w$ are linearly independent, so $P = K v + K w$ has dimension $2$ and $\mathbb{P}(P)$ is a line through $x$ and $y$. If $Q$ is another submodule of dimension $2$ with $x, y \in \mathbb{P}(Q)$, then $v, w \in Q$, so $P \subseteq Q$, and equal dimensions give $P = Q$. $\square$

<?decl Projectivization.line_unique?>

**Theorem (Two lines in a plane meet).** Let $\dim V = 3$, so that $\mathbb{P}(V)$ is a projective plane. Two distinct lines of $\mathbb{P}(V)$ meet in exactly one point.

*Proof.* Let the lines be $\mathbb{P}(W_1)$ and $\mathbb{P}(W_2)$ with $\dim W_1 = \dim W_2 = 2$ and $W_1 \neq W_2$. Then $W_1 + W_2$ strictly contains $W_1$, so it is $V$, and the dimension formula gives $\dim (W_1 \cap W_2) = 2 + 2 - 3 = 1$. Its projectivization is a single point. $\square$

<?decl Submodule.finrank_sup_add_finrank_inf_eq?>

**Proposition (Lines of $\mathbb{P}^2$ by the cross product).** Let $K$ be a field and $V = K^3$, with the cross product $\times$ and the dot product $\cdot$.

1. For $v, w \neq 0$, $[v] = [w]$ if and only if $v \times w = 0$.
2. If $[v] \neq [w]$, the line through $[v]$ and $[w]$ is the set of points $[u]$ with $(v \times w) \cdot u = 0$.
3. Dually, the lines $\{[u] : a \cdot u = 0\}$ and $\{[u] : b \cdot u = 0\}$ with $[a] \neq [b]$ meet at the point $[a \times b]$.

*Proof.* (1) The coordinates of $v \times w$ are the $2 \times 2$ minors of the matrix with rows $v$ and $w$. They all vanish if and only if $v$ and $w$ are dependent. (2) Let $n = v \times w$, nonzero by (1). Since $n \cdot u = \det(v, w, u)$, $n \cdot v = n \cdot w = 0$, so $K v + K w$ lies in the kernel of $u \mapsto n \cdot u$; both have dimension $2$. (3) The vector $a \times b$ is nonzero by (1), and $a \cdot (a \times b) = b \cdot (a \times b) = 0$, so $[a \times b]$ lies on both lines; it is the only common point. $\square$

::: mathlib
`Projectivization.cross` · `Mathlib.LinearAlgebra.Projectivization.Constructions`

The cross product on $\mathbb{P}(F^3)$, returning the first point when $v \times w = 0$. The relation `orthogonal` means $v \cdot w = 0$.

<?decl Projectivization.cross?>
:::

<?decl Projectivization.cross_mk?>

<?decl Projectivization.mk_eq_mk_iff_crossProduct_eq_zero?>

<?decl Projectivization.orthogonal_mk?>

**Theorem (Transitivity of the linear group).** The group $\mathrm{GL}(V)$ acts $2$-transitively on $\mathbb{P}(V)$: for points $x_1 \neq x_2$ and $y_1 \neq y_2$ there is $g$ with $g x_1 = y_1$ and $g x_2 = y_2$.

*Proof.* Write $x_i = [v_i]$ and $y_i = [w_i]$. The pairs $v_1, v_2$ and $w_1, w_2$ are linearly independent. Extend them to bases $v_1, v_2, (e_j)$ and $w_1, w_2, (f_j)$ with the same index set. The linear map with $v_i \mapsto w_i$ and $e_j \mapsto f_j$ sends a basis to a basis, so it is invertible, and it sends $x_i$ to $y_i$. $\square$

<?decl Projectivization.generalLinearGroup_is_two_pretransitive?>

**Theorem (Kernel of the action).** Let $K$ be a field. An element $g \in \mathrm{GL}(V)$ fixes every point of $\mathbb{P}(V)$ if and only if $g$ is a scalar multiple of the identity. Hence $\mathrm{PGL}_n(K)$ acts faithfully on $\mathbb{P}^{n-1}(K)$, and the kernel of the action of $\mathrm{SL}_n(K)$ is its center, the scalar matrices $\lambda I$ with $\lambda^n = 1$.

*Proof.* Scalars fix every line. Conversely, if $g$ fixes every point, every nonzero $v$ is an eigenvector: $g v = \lambda_v v$. For independent $v$ and $w$, $g (v + w) = \lambda_{v + w} (v + w)$ and also $g(v + w) = \lambda_v v + \lambda_w w$; comparing coefficients gives $\lambda_v = \lambda_{v+w} = \lambda_w$. Dependent vectors give equal values directly, so $g = \lambda \cdot \mathrm{id}$. The scalar matrices in $\mathrm{SL}_n(K)$ are those with $\lambda^n = 1$, and they form its center. $\square$

<?decl Projectivization.SL_mulAction_ker?>

**Theorem (Simplicity of $\mathrm{PSL}_2$).** Let $F$ be a field with at least $4$ elements. Then $\mathrm{PSL}_2(F)$ is a simple group.

The proof applies Iwasawa's criterion to the $2$-transitive action on $\mathbb{P}^1(F)$, with the transvections and the perfectness of $\mathrm{PSL}_2(F)$; it belongs to group theory and is not given here.

::: mathlib
`Matrix.ProjectiveSpecialLinearGroup.rank_two_simple` · `Mathlib.LinearAlgebra.Projectivization.PSL.PSL2`

The hypothesis is `4 ≤ Nat.card F`. Since `Nat.card` of an infinite type is $0$, the statement covers only finite fields, although the paper theorem holds for infinite fields too.

<?decl Matrix.ProjectiveSpecialLinearGroup.rank_two_simple?>
:::

### Examples

**Example (A line of the Fano plane).** In $\mathbb{P}^2(\mathbb{F}_2)$ take $[1:1:0]$ and $[0:1:1]$. Their cross product is $(1, -1, 1) = (1, 1, 1)$ in $\mathbb{F}_2$. The line is $x + y + z = 0$, with points $[1:1:0]$, $[0:1:1]$ and $[1:0:1]$, the third being the sum of the first two.

**Example (Orders of $\mathrm{PGL}_2(\mathbb{F}_q)$ and $\mathrm{PSL}_2(\mathbb{F}_q)$).** A matrix in $\mathrm{GL}_2(\mathbb{F}_q)$ has a nonzero first column ($q^2 - 1$ choices) and a second column outside its span ($q^2 - q$ choices). Dividing by the $q - 1$ scalars gives $|\mathrm{PGL}_2(\mathbb{F}_q)| = q (q^2 - 1)$. Since $|\mathrm{SL}_2(\mathbb{F}_q)| = q(q^2 - 1)$ and its center has $\gcd(2, q - 1)$ elements, $|\mathrm{PSL}_2(\mathbb{F}_q)| = q (q^2 - 1)/\gcd(2, q - 1)$, which is $60$ for $q = 4$ and $q = 5$.

**Counterexample ($\mathrm{PSL}_2(\mathbb{F}_2)$ and $\mathrm{PSL}_2(\mathbb{F}_3)$ are not simple).** For $q = 2$ the center is trivial and $\mathrm{PSL}_2(\mathbb{F}_2) = \mathrm{GL}_2(\mathbb{F}_2)$ has order $6$. It acts faithfully on the $3$ points of $\mathbb{P}^1(\mathbb{F}_2)$, so it is isomorphic to $S_3$, which has the normal subgroup $A_3$. For $q = 3$ the group $\mathrm{PSL}_2(\mathbb{F}_3)$ has order $12$ and acts faithfully on the $4$ points of $\mathbb{P}^1(\mathbb{F}_3)$, so it is a subgroup of order $12$ of $S_4$, namely $A_4$, which has the normal Klein subgroup of order $4$. The hypothesis $|F| \geq 4$ is therefore needed.

**Counterexample (No $3$-transitivity on $\mathbb{P}^2$).** $\mathrm{GL}_3(K)$ is not $3$-transitive on $\mathbb{P}^2(K)$. The points $[1:0:0]$, $[0:1:0]$, $[1:1:0]$ are collinear and $[1:0:0]$, $[0:1:0]$, $[0:0:1]$ are not. Invertible maps preserve collinearity, so no element maps the first triple to the second.

### The library around it

The subspace file gives the lattice, the span with its Galois insertion `Projectivization.Subspace.gi`, and the isomorphism with submodules, through which most results are proved. The action file covers $\mathrm{GL}(V)$, $\mathrm{SL}(V)$ and `Matrix.ProjGenLinGroup`; $2$-transitivity is an instance.

The index of this edition has no declaration for the fundamental theorem of projective geometry, which identifies the line-preserving bijections of $\mathbb{P}(V)$ with semilinear maps when $\dim V \geq 3$, nor for Desargues' theorem.

<?decl Projectivization.Subspace.subset_span?>

<?decl Projectivization.Subspace.gi?>

<?decl Projectivization.isCollinear_pair?>

<?decl Projectivization.specialLinearGroup_is_two_pretransitive?>

The file `Mathlib.LinearAlgebra.Projectivization.PSL.Stabilizer` prepares a proof that $\mathrm{PSL}_n(F)$ is simple by the criterion of Iwasawa. For a subspace $L \subseteq F^n$, `Matrix.SpecialLinearGroup.lineStab L` is the subgroup of the $A \in \mathrm{SL}_n(F)$ with $A w - w \in L$ for all $w$ (`Matrix.SpecialLinearGroup.mem_lineStab_iff`). When $L$ is a line $F v$, such an $A$ has the form $w \mapsto w + \alpha(w) v$ for a linear form $\alpha$, and $\det A = 1 + \alpha(v)$. So $\alpha(v) = 0$ and $A v = v$ (`Matrix.SpecialLinearGroup.lineStab_fix_of_span`). Two such matrices commute, because $(1 + v \alpha)(1 + v \beta) = 1 + v (\alpha + \beta)$ when $\alpha(v) = 0$ (`Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span`). Conjugation by $g$ carries the subgroup of $L$ to the subgroup of $g L$ (`Matrix.SpecialLinearGroup.lineStab_smul`). The images `PSL.iwasawaT p` in $\mathrm{PSL}_n(F)$, one for each point $p$ of the projective space, are the abelian subgroups that the criterion of Iwasawa needs.

### Exercises

1. (A) Find the line of $\mathbb{P}^2(\mathbb{Q})$ through $[1:2:3]$ and $[0:1:1]$, as an equation $a x + b y + c z = 0$. Hint: compute the cross product and check both points.

2. (A) Find the intersection point of the lines $x + y + z = 0$ and $x - y = 0$ in $\mathbb{P}^2(\mathbb{R})$. Hint: the cross product of the normal vectors.

3. (B) Show that the union of two subspaces $T_1$ and $T_2$ of $\mathbb{P}(V)$ is a subspace if and only if $T_1 \subseteq T_2$ or $T_2 \subseteq T_1$. Hint: if $[v] \in T_1 \setminus T_2$ and $[w] \in T_2 \setminus T_1$, look at $[v + w]$.

4. (B) Prove that for subspaces of a finite-dimensional $\mathbb{P}(V)$, $\dim (T_1 \vee T_2) + \dim (T_1 \cap T_2) = \dim T_1 + \dim T_2$, with the convention $\dim \emptyset = -1$. Deduce that a line and a plane in $\mathbb{P}^3$ always meet. Hint: translate to submodules.

5. (B) Show that $\mathrm{PGL}_2(K)$ acts sharply $3$-transitively on $\mathbb{P}^1(K)$: for distinct $x_1, x_2, x_3$ and distinct $y_1, y_2, y_3$ there is exactly one element mapping each $x_i$ to $y_i$. Hint: reduce to $y = (\infty, 0, 1)$ and find the matrix sending $[v_1], [v_2], [v_3]$ there.

6. (B) Use Exercise 5 to show that $\mathrm{PGL}_2(\mathbb{F}_q)$ has order $(q + 1) q (q - 1)$, and compare with the count in the Examples.

### Notes and history

Projective geometry grew from the study of perspective; Poncelet developed it in the early nineteenth century and von Staudt gave it a foundation without measurement. Homogeneous coordinates are due to Möbius and Plücker. Jordan proved the simplicity of the projective special linear groups over prime fields, and Dickson extended it to all finite fields. Iwasawa's criterion dates from 1941.

### Reference

<?reference?>
