---
title: The exchange lemma and the invariance of dimension
kind: theory
modules:
  - Mathlib.LinearAlgebra.LinearIndependent.Lemmas
  - Mathlib.LinearAlgebra.Basis.VectorSpace
  - Mathlib.LinearAlgebra.Dimension.Basic
  - Mathlib.LinearAlgebra.Dimension.StrongRankCondition
  - Mathlib.LinearAlgebra.InvariantBasisNumber
explains:
  E3: [mem_span_insert_exchange, Module.rank, mk_eq_mk_of_basis, Module.Basis.ofVectorSpace]
  E2: [exists_linearIndependent, Module.Basis.extend, StrongRankCondition, InvariantBasisNumber, Module.Basis.mk_eq_rank, linearIndependent_le_span_finset, Submodule.exists_isCompl]
  E1: auto
families: []
requires: [V07.C01, V01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The exchange lemma and the invariance of dimension

### Overview

A vector space has many bases. The plane $\mathbb{R}^2$ has the basis $e_1, e_2$, the basis $(1, 1), (1, -1)$, and infinitely many more. Each of them has two vectors. This section proves that this is a general fact: two bases of a vector space have the same number of elements, finite or infinite. This number is the dimension. The proof rests on one step, the exchange lemma: a vector of a spanning family can be traded for a vector of an independent family, and the new family still spans. Repeated, the step shows that an independent family is never larger than a spanning family.

The section also proves that each vector space has a basis, that each independent family extends to a basis, and that each subspace has a complement. These facts need a field, or at least a division ring. Over a commutative ring, bases need not exist, but when they do, they still have the same size. Mathlib records this with the classes `InvariantBasisNumber` and `StrongRankCondition`, and it defines the rank `Module.rank` of each module as a cardinal.

### Definitions

**Definition (Rank).** The rank of an $R$-module $M$ is the supremum of the cardinals of the linearly independent subsets of $M$:
$$\operatorname{rank}_R M = \sup \{ |S| : S \subseteq M \text{ linearly independent} \}.$$
When $R$ is a field, the rank is the dimension $\dim_R M$.

::: mathlib
`Module.rank` · `Mathlib.LinearAlgebra.Dimension.Basic`

The rank `Module.rank R M : Cardinal`, defined as the supremum `⨆ ι : {s : Set M // LinearIndepOn R id s}, #ι.val`. The definition does not ask for a basis, so it makes sense for each module. For a vector space, the theorems below show that it is the cardinal of each basis. For the module $\mathbb{Q}$ over $\mathbb{Z}$, which has no basis, the rank is $1$.

<?decl Module.rank?>
:::

**Definition (Invariant basis number).** A ring $R$ has invariant basis number if $R^n \cong R^m$ as $R$-modules implies $n = m$. It satisfies the strong rank condition if each injective linear map $R^n \to R^m$ has $n \le m$.

::: mathlib
`InvariantBasisNumber` · `Mathlib.LinearAlgebra.InvariantBasisNumber`

The class `InvariantBasisNumber R`, with the field `eq_of_fin_equiv : ((Fin n → R) ≃ₗ[R] (Fin m → R)) → n = m`. It is the condition that the rank of a finite free module is well defined. Each nontrivial commutative ring has it, by the instance `invariantBasisNumber_of_nontrivial_of_commRing`.

<?decl InvariantBasisNumber?>
:::

::: mathlib
`StrongRankCondition` · `Mathlib.LinearAlgebra.InvariantBasisNumber`

The class `StrongRankCondition R`: an injective linear map `(Fin n → R) →ₗ[R] (Fin m → R)` forces `n ≤ m`. It implies `InvariantBasisNumber`. Each division ring, each nontrivial left Noetherian ring and each nontrivial commutative ring satisfies it. Most theorems on the rank of a free module ask for this class, since it gives the comparison between an independent family and a basis.

<?decl StrongRankCondition?>
:::

### Theorems and proofs

In this part, $K$ is a field and $V$ is a vector space over $K$. The proofs work word for word over a division ring.

**Theorem (Exchange lemma).** Let $S \subseteq V$, and let $x, y \in V$. If $x \in \operatorname{span}(S \cup \{y\})$ and $x \notin \operatorname{span} S$, then $y \in \operatorname{span}(S \cup \{x\})$.

*Proof.* Since $x \in \operatorname{span}(S \cup \{y\})$, there are $a \in K$ and $z \in \operatorname{span} S$ with $x = a y + z$. If $a = 0$, then $x = z \in \operatorname{span} S$, against the hypothesis. So $a \neq 0$, and
$$y = a^{-1} x - a^{-1} z.$$
The vector $a^{-1} x$ lies in $\operatorname{span}(S \cup \{x\})$, and $a^{-1} z$ lies in $\operatorname{span} S \subseteq \operatorname{span}(S \cup \{x\})$. So $y \in \operatorname{span}(S \cup \{x\})$. $\square$

Under the hypotheses, the two sets $S \cup \{x\}$ and $S \cup \{y\}$ have the same span: each contains the other set in its span.

::: mathlib
`mem_span_insert_exchange` · `Mathlib.LinearAlgebra.LinearIndependent.Lemmas`

The statement `x ∈ span K (insert y s) → x ∉ span K s → y ∈ span K (insert x s)`, for a vector space over a division ring `K`. The proof in Mathlib is the proof above: it writes `x = a • y + z` and takes `a⁻¹`.

<?decl mem_span_insert_exchange?>
:::

**Theorem (Steinitz exchange theorem).** Let $(v_1, \dots, v_m)$ be a linearly independent family in $V$, and let $(w_1, \dots, w_n)$ be a family that spans $V$. Then $m \le n$, and the $w_j$ can be renumbered so that $(v_1, \dots, v_m, w_{m+1}, \dots, w_n)$ spans $V$.

*Proof.* Prove by induction on $k$, for $0 \le k \le m$, the claim $C(k)$: $k \le n$, and after a renumbering of the $w_j$, the family $(v_1, \dots, v_k, w_{k+1}, \dots, w_n)$ spans $V$. The claim $C(0)$ is the hypothesis.

Suppose $C(k)$ holds with $k < m$. The vector $v_{k+1}$ lies in $V$, which is the span of $(v_1, \dots, v_k, w_{k+1}, \dots, w_n)$. So
$$v_{k+1} = a_1 v_1 + \dots + a_k v_k + b_{k+1} w_{k+1} + \dots + b_n w_n$$
for some scalars. If all the $b_j$ are $0$, or if there is no $w_j$ left, that is $k = n$, then $v_{k+1}$ is a combination of $v_1, \dots, v_k$. This contradicts the independence of the $v_i$. So $k < n$, and some $b_j \neq 0$. Renumber $w_{k+1}, \dots, w_n$ so that $b_{k+1} \neq 0$.

From the displayed equation and $b_{k+1} \neq 0$,
$$w_{k+1} = b_{k+1}^{-1} \Big( v_{k+1} - \sum_{i \le k} a_i v_i - \sum_{j \ge k+2} b_j w_j \Big).$$
So $w_{k+1}$ lies in the span of the family $F = (v_1, \dots, v_{k+1}, w_{k+2}, \dots, w_n)$. The span of $F$ thus contains each vector of the old spanning family $(v_1, \dots, v_k, w_{k+1}, \dots, w_n)$, so it is $V$. This is $C(k+1)$, with $k + 1 \le n$.

By induction, $C(m)$ holds, and it gives $m \le n$ and the spanning family. $\square$

The induction step is the exchange lemma in a computed form. Put $S = \{v_1, \dots, v_k, w_{k+2}, \dots, w_n\}$, $x = v_{k+1}$ and $y = w_{k+1}$. The step shows that $y$ lies in the span of $S \cup \{x\}$, and this is the conclusion of the exchange lemma. The division by $b_{k+1}$ is the only place where the field is used.

::: mathlib
`linearIndependent_le_span_finset` · `Mathlib.LinearAlgebra.Dimension.StrongRankCondition`

The bound of the Steinitz theorem: if `v : ι → M` is independent and the finite set `w` spans `M`, then `#ι ≤ w.card`. It holds over each ring with `StrongRankCondition`, not only over fields. The proof in Mathlib goes through an injective map into a free module of finite rank, not through the exchange.

<?decl linearIndependent_le_span_finset?>
:::

**Corollary (Invariance of dimension, finite case).** Let $V$ have a finite basis $(b_1, \dots, b_n)$. Then each basis of $V$ has $n$ elements.

*Proof.* Let $(c_i)_{i \in I}$ be another basis. Each finite subfamily of the $c_i$ is independent, and $(b_1, \dots, b_n)$ spans, so each finite subfamily has at most $n$ elements by the Steinitz theorem. So $I$ is finite and $|I| \le n$. Now $(c_i)$ spans and $(b_j)$ is independent, so $n \le |I|$ by the same theorem. $\square$

**Theorem (Existence of bases).** Let $L \subseteq V$ be a linearly independent set and $G \supseteq L$ a set that spans $V$. Then there is a basis $B$ of $V$ with $L \subseteq B \subseteq G$. In particular each vector space has a basis, each independent set extends to a basis, and each spanning set contains a basis.

*Proof.* Let $\mathcal{P}$ be the set of the independent sets $B$ with $L \subseteq B \subseteq G$, ordered by inclusion. It contains $L$. Let $\mathcal{C}$ be a nonempty chain in $\mathcal{P}$, and let $U = \bigcup \mathcal{C}$. Then $L \subseteq U \subseteq G$. The set $U$ is independent: a relation $\sum c_i u_i = 0$ uses finitely many vectors $u_1, \dots, u_r$ of $U$, each $u_i$ lies in some $B_i \in \mathcal{C}$, and the largest of $B_1, \dots, B_r$ in the chain contains all of them. That set is independent, so the $c_i$ are $0$. So each chain has an upper bound in $\mathcal{P}$, and Zorn's lemma gives a maximal element $B$.

The set $B$ spans $V$. It suffices to show $G \subseteq \operatorname{span} B$, since $G$ spans. Let $g \in G$. If $g \notin \operatorname{span} B$, then $B \cup \{g\}$ is independent by the test of Section 1, and $L \subseteq B \cup \{g\} \subseteq G$. This contradicts the maximality of $B$. So $B$ is independent and spans, and it is a basis. For the special cases, take $L = \emptyset$ and $G = V$; or $G = V$; or $L = \emptyset$. $\square$

::: mathlib
`exists_linearIndependent` · `Mathlib.LinearAlgebra.LinearIndependent.Lemmas`

Each set `t` contains an independent set `b` with the same span: `∃ b ⊆ t, span K b = span K t ∧ LinearIndependent K ((↑) : b → V)`. With `t` a spanning set, `b` is a basis. The proof uses Zorn's lemma through `exists_linearIndepOn_id_extension`.

<?decl exists_linearIndependent?>
:::

::: mathlib
`Module.Basis.extend` · `Mathlib.LinearAlgebra.Basis.VectorSpace`

The basis `Module.Basis.extend hs` that extends an independent set `s`. Its index type is the set `hs.extend (subset_univ s)`, which contains `s`. The lemma `Module.Basis.extend_apply_self` says that its vectors are the elements of the index set.

<?decl Module.Basis.extend?>
:::

::: mathlib
`Module.Basis.ofVectorSpace` · `Mathlib.LinearAlgebra.Basis.VectorSpace`

A basis of a vector space `V` over a division ring `K`: `Module.Basis.ofVectorSpace K V`, indexed by a set `ofVectorSpaceIndex K V`. It is `Basis.extend` of the empty set, so it is chosen by the axiom of choice and does not compute. Its existence gives the instance `Module.Free.of_divisionRing`: each vector space is a free module.

<?decl Module.Basis.ofVectorSpace?>
:::

**Theorem (Invariance of dimension).** Any two bases of $V$ have the same cardinal.

*Proof.* Let $B$ and $C$ be bases of $V$. If one of them is finite, the finite case applies. Suppose both are infinite. Each $c \in C$ is a combination of a finite set $F_c \subseteq B$. The union $\bigcup_{c \in C} F_c$ spans a subspace that contains $C$, so it spans $V$. If some $b \in B$ is not in this union, then $b$ is a combination of the vectors of $B \setminus \{b\}$, which contradicts the independence of $B$. So $B = \bigcup_{c \in C} F_c$. This is a union of $|C|$ finite sets, so $|B| \le |C| \cdot \aleph_0 = |C|$, since $C$ is infinite. By symmetry $|C| \le |B|$, and the theorem of Cantor, Schröder and Bernstein gives $|B| = |C|$. $\square$

::: mathlib
`mk_eq_mk_of_basis` · `Mathlib.LinearAlgebra.Dimension.StrongRankCondition`

Two bases `v : Basis ι R M` and `v' : Basis ι' R M` have index types of the same cardinal: `Cardinal.lift #ι = Cardinal.lift #ι'`. The `lift` is there because `ι` and `ι'` may live in different universes. The theorem holds over each ring with `InvariantBasisNumber`. The proof splits into the finite and the infinite case, as above.

<?decl mk_eq_mk_of_basis?>
:::

**Theorem (Rank of a free module).** Let $R$ satisfy the strong rank condition, and let $(b_i)_{i \in \iota}$ be a basis of $M$. Then $\operatorname{rank}_R M = |\iota|$. If $\iota$ is finite and $(v_j)_{j \in J}$ is independent in $M$, then $|J| \le |\iota|$.

*Proof.* For a field, the Steinitz theorem gives the second claim, and with the argument of the infinite case it shows that each independent set has cardinal at most $|\iota|$. The basis itself is independent, so the supremum that defines the rank is $|\iota|$. For a general ring with the strong rank condition, a finite independent family $(v_1, \dots, v_k)$ gives an injective map $R^k \to M \cong R^n$, so $k \le n$ by the definition of the condition. $\square$

::: mathlib
`Module.Basis.mk_eq_rank` · `Mathlib.LinearAlgebra.Dimension.StrongRankCondition`

The rank is the cardinal of a basis: `Cardinal.lift #ι = Cardinal.lift (Module.rank R M)`. For a finite basis, the form with `Fintype.card` is `rank_eq_card_basis`.

<?decl Module.Basis.mk_eq_rank?>
:::

**Theorem (Complements).** Each subspace $W$ of $V$ has a complement: a subspace $W'$ with $W \cap W' = 0$ and $W + W' = V$.

*Proof.* Choose a basis $B_W$ of $W$, and extend it to a basis $B$ of $V$ by the existence theorem. Let $W' = \operatorname{span}(B \setminus B_W)$. Then $W + W'$ contains $B$, so it is $V$. If $x \in W \cap W'$, then $x$ is a combination of $B_W$ and also a combination of $B \setminus B_W$. The difference of the two expressions is a relation among the vectors of $B$, so all the coefficients are $0$, and $x = 0$. $\square$

::: mathlib
`Submodule.exists_isCompl` · `Mathlib.LinearAlgebra.Basis.VectorSpace`

Each subspace `p` of a vector space has a complement: `∃ q, IsCompl p q`. The predicate `IsCompl p q` from the lattice library means `p ⊓ q = ⊥` and `p ⊔ q = ⊤`. The instance `Submodule.complementedLattice` records that the lattice of subspaces is complemented. Over `ℤ` this fails: the submodule $2 \mathbb{Z}$ of $\mathbb{Z}$ has no complement.

<?decl Submodule.exists_isCompl?>
:::

### Examples

**Example (An exchange in $\mathbb{Q}^3$).** Take the spanning family $w_1 = e_1$, $w_2 = e_2$, $w_3 = e_3$ and the independent family $v_1 = (1, 1, 0)$, $v_2 = (0, 1, 1)$. Step 1: $v_1 = 1 \cdot w_1 + 1 \cdot w_2 + 0 \cdot w_3$, and $b_1 = 1 \neq 0$. Trade $w_1$ for $v_1$: the family $(v_1, e_2, e_3)$ spans, since $e_1 = v_1 - e_2$. Step 2: write $v_2$ in the new family: $v_2 = 0 \cdot v_1 + 1 \cdot e_2 + 1 \cdot e_3$. The coefficient of $e_2$ is $1 \neq 0$. Trade $e_2$ for $v_2$: the family $(v_1, v_2, e_3)$ spans, since $e_2 = v_2 - e_3$. So $(v_1, v_2, e_3)$ is a spanning family of three vectors in a space of dimension $3$, and it is a basis by Section 3.

**Example (A spanning family reduced to a basis).** In $\mathbb{R}^3$, let $G = \{g_1, g_2, g_3, g_4\}$ with $g_1 = (1, 0, 1)$, $g_2 = (2, 0, 2)$, $g_3 = (0, 1, 1)$ and $g_4 = (1, 1, 2)$. Keep $g_1$. Drop $g_2 = 2 g_1$. Keep $g_3$, since it is not a multiple of $g_1$. Drop $g_4 = g_1 + g_3$. So $\{g_1, g_3\}$ is a basis of $\operatorname{span} G$, and this span is a plane. It is the plane $x_1 + x_2 = x_3$: both $g_1$ and $g_3$ satisfy the equation, and a plane through $0$ is fixed by two independent vectors.

**Example (The rank of $\mathbb{Q}$ over $\mathbb{Z}$).** Two nonzero rationals are dependent over $\mathbb{Z}$, as shown in Section 1. So the independent subsets of $\mathbb{Q}$ have at most one element, and $\{1\}$ is independent. Thus $\operatorname{rank}_{\mathbb{Z}} \mathbb{Q} = 1$, although $\mathbb{Q}$ has no basis over $\mathbb{Z}$. The rank of $\mathbb{Z}/n$ over $\mathbb{Z}$ is $0$, since $n \cdot x = 0$ for each $x$.

**Counterexample (A ring without invariant basis number).** Let $V$ be a vector space over $K$ with a countable basis $e_0, e_1, \dots$, and let $E = \operatorname{End}_K(V)$. Then $E \cong E^2$ as left $E$-modules. The map sends $f$ to the pair $(f \circ \iota_0, f \circ \iota_1)$, where $\iota_0(e_n) = e_{2n}$ and $\iota_1(e_n) = e_{2n+1}$. So the noncommutative ring $E$ has bases of $1$ and of $2$ elements on the same module. This is why Mathlib makes invariant basis number a class and does not prove it for all rings.

### The library around it

The exchange lemma and the extension of independent sets are in `Mathlib.LinearAlgebra.LinearIndependent.Lemmas`. The existence of bases and of complements for vector spaces is in `Mathlib.LinearAlgebra.Basis.VectorSpace`. The definition of `Module.rank` is in `Mathlib.LinearAlgebra.Dimension.Basic`, and the comparison of bases over rings with the strong rank condition is in `Mathlib.LinearAlgebra.Dimension.StrongRankCondition`. The classes on rings are in `Mathlib.LinearAlgebra.InvariantBasisNumber`. The proof that each commutative ring satisfies the strong rank condition is in the ring theory library, `commRing_strongRankCondition`.

The rank is a cardinal, and cardinals live in universes. Many statements on the rank carry `Cardinal.lift`. For a learner, the simpler path is often `Module.finrank` of Section 3, a natural number.

### Exercises

1. (A) Extend the independent family $(1, 2, 3)$ to a basis of $\mathbb{Q}^3$ with vectors of the standard basis. Hint: follow the proof of Steinitz with $w_j = e_j$.
2. (A) Show that a family of $n + 1$ vectors in $K^n$ is dependent.
3. (A) Find a basis of the subspace $\{x \in \mathbb{R}^4 : x_1 + x_2 + x_3 + x_4 = 0\}$ and a complement of it.
4. (B) Show that a spanning family of $n$ vectors in a space of dimension $n$ is a basis, and that an independent family of $n$ vectors is a basis.
5. (B) Show that $2 \mathbb{Z}$ has no complement in $\mathbb{Z}$. Hint: two nonzero submodules of $\mathbb{Z}$ meet in a nonzero submodule.
6. (B) Let $V$ be a vector space over $\mathbb{F}_q$ of dimension $n$. Show that $|V| = q^n$, and count the bases of $V$. Hint: choose the vectors one at a time; the $k$-th vector avoids a subspace of $q^{k-1}$ elements.
7. (B) Show that $\operatorname{rank}_{\mathbb{Z}} \mathbb{Z}^n = n$, and that $\mathbb{Z}^n$ contains independent families of $n$ vectors that are not bases.
8. (C) Prove the exchange theorem for infinite families: if $L$ is independent and $G$ spans $V$, then $|L| \le |G|$. Hint: each element of $L$ lies in the span of a finite subset of $G$; follow the proof of the invariance of dimension.
9. (C) Check the isomorphism $E \cong E^2$ of the counterexample: show that the map $f \mapsto (f \iota_0, f \iota_1)$ is $E$-linear and bijective. Hint: the inverse sends $(g, h)$ to the map $e_{2n} \mapsto g(e_n)$, $e_{2n+1} \mapsto h(e_n)$.

### Notes and history

Ernst Steinitz proved the exchange theorem in 1913, in a paper on algebraic configurations. Hermann Grassmann had used the idea in 1862 in the second edition of his "Ausdehnungslehre". The existence of a basis of each vector space, and of a Hamel basis of $\mathbb{R}$ over $\mathbb{Q}$, is due to Georg Hamel in 1905, who used the well ordering theorem. In 1984, Andreas Blass proved that the existence of bases in all vector spaces implies the axiom of choice.

The choice to define the rank as a supremum over independent sets, and not as the cardinal of a basis, gives a rank to each module and makes many statements hold without a hypothesis of freeness.

### Reference

<?reference?>
