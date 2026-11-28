---
title: Pointwise operations, bimodules, congruences and graded modules
kind: api
modules:
  - Mathlib.Algebra.Module.Submodule.Pointwise
  - Mathlib.Algebra.Module.Submodule.Bilinear
  - Mathlib.Algebra.Module.Congruence.Defs
  - Mathlib.Algebra.Module.Bimodule
  - Mathlib.Algebra.Module.GradedModule
  - Mathlib.LinearAlgebra.SModEq.Basic
  - Mathlib.LinearAlgebra.SModEq.Pointwise
  - Mathlib.LinearAlgebra.SModEq.Pow
  - Mathlib.LinearAlgebra.Quotient.Card
explains:
  E2: [Submodule.add_eq_sup, Submodule.mem_smul_pointwise_iff_exists, Submodule.set_smul_le_iff, Submodule.map₂, Submodule.map₂_span_span, ModuleCon, ModuleCon.quotientKerEquivOfSurjective, Subbimodule.mk, DirectSum.Gmodule, SModEq]
  E1: auto
families: []
requires: [V04, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Pointwise operations, bimodules, congruences and graded modules

### Overview

The set of submodules of a module is a complete lattice, and Mathlib also gives it algebraic operations. Two submodules have a sum, a scalar can act on a submodule, and a set of scalars can act on a submodule. A bilinear map sends a pair of submodules to the submodule spanned by the values. This section describes these operations. The sum is always available, and the actions of scalars become available after `open Pointwise`. It then treats three related structures: the equivalence relations on a module that respect its operations, the submodules of a bimodule, and the modules over a graded ring that are graded themselves.

### The library around it

#### The sum of submodules

The pointwise sum of two submodules is the set $\{x + y : x \in p, y \in q\}$. This set is already a submodule, and it is the join $p \sqcup q$.

**Theorem.** For submodules $p, q \le M$, the set $p + q$ is equal to $p \sqcup q$.

*Proof.* The set $p + q$ contains $p$ and $q$, and each submodule that contains $p$ and $q$ contains $p + q$. It is enough to show that $p + q$ is a submodule. It contains $0 = 0 + 0$. It is closed under addition, since $(x + y) + (x' + y') = (x + x') + (y + y')$, and under the action, since $c (x + y) = c x + c y$. $\square$

This is `Submodule.add_eq_sup`. The instance `Submodule.pointwiseAddCommMonoid` makes the submodules into a commutative monoid with $0 = \bot$ (`Submodule.zero_eq_bot`). The order is the canonical order of this monoid, by the instances `Submodule.instIsOrderedAddMonoid` and `Submodule.instCanonicallyOrderedAdd`. The pointwise negation $-p = \{-x : x \in p\}$ is again $p$ (`Submodule.neg_eq_self`) over a ring, but over a semiring it is a separate operation with `Submodule.mem_neg` and the order isomorphism `Submodule.negOrderIso`.

#### Scalars acting on submodules

Let $\alpha$ be a monoid that acts on $M$ by maps that commute with the $R$-action, for example $R$ itself when $R$ is commutative. An element $a \in \alpha$ sends a submodule $S$ to its image $a \cdot S$, by the instance `Submodule.pointwiseDistribMulAction`. The definition is `Submodule.pointwise_smul_def`: $a \cdot S$ is the image of $S$ under the map $x \mapsto a x$. The membership lemma is `Submodule.mem_smul_pointwise_iff_exists : m ∈ a • S ↔ ∃ b ∈ S, a • b = m`, and `Submodule.smul_mem_pointwise_smul` is the easy direction. The action commutes with joins (`Submodule.smul_sup'`, `Submodule.smul_iSup'`), and a unit of $R$ fixes each submodule (`Submodule.smul_eq_self_of_isUnit`). For a group $G$ that acts on $M$, the stabilizer of $S$ is the set of $g$ with $g S = S$ (`Submodule.mem_stabilizer_submodule_iff_map_eq`).

A set of scalars $s$ also acts on a submodule. The product $s \cdot N$ is the smallest submodule that contains $r x$ for each $r \in s$ and $x \in N$. The universal property is `Submodule.set_smul_le_iff : s • N ≤ p ↔ ∀ r ∈ s, ∀ n ∈ N, r • n ∈ p`, and the induction principle is `Submodule.set_smul_inductionOn`. The product is a join of the scalar actions, `Submodule.set_smul_eq_iSup`, and a singleton gives the action of one element (`Submodule.singleton_set_smul`). When $s$ is an ideal $I$ of $R$, this product is the submodule $I N$ of commutative algebra, written `I • N`.

#### Bilinear images of submodules

Let $f : M \to N \to P$ be a bilinear map and $p \le M$, $q \le N$. The submodule `Submodule.map₂ f p q` is the span of the values $f(m, n)$ with $m \in p$, $n \in q$.

**Theorem.** For sets $s \subseteq M$ and $t \subseteq N$, the bilinear image of $\operatorname{span}(s)$ and $\operatorname{span}(t)$ is the span of $\{f(m, n) : m \in s, n \in t\}$.

*Proof.* The inclusion from right to left is clear. For the other inclusion, let $Q$ be the right side. For a fixed $n \in t$, the set of $m$ with $f(m, n) \in Q$ is a submodule that contains $s$, so it contains $\operatorname{span}(s)$. Then, for a fixed $m \in \operatorname{span}(s)$, the set of $n$ with $f(m, n) \in Q$ is a submodule that contains $t$, so it contains $\operatorname{span}(t)$. $\square$

This is `Submodule.map₂_span_span`. The universal property is `Submodule.map₂_le`, and `Submodule.apply_mem_map₂` puts each value in the image. The bilinear image is monotone in each variable (`Submodule.map₂_le_map₂`), preserves joins in each variable (`Submodule.map₂_sup_left`, `Submodule.map₂_iSup_right`), and sends $\bot$ to $\bot$. The rules with linear maps are `Submodule.map₂_map_left`, `Submodule.map_map₂` and `Submodule.map₂_flip`. With $f$ the multiplication of an algebra, `Submodule.map₂` gives the product of two submodules of the algebra.

#### Congruences

A submodule $p \le M$ gives an equivalence relation, $x \sim y$ if $x - y \in p$. Over a semiring there are no differences, and the quotient constructions use congruences in their place. A `ModuleCon S M` is an additive congruence on $M$, an equivalence relation that respects the sum, that also respects the action: $x \sim y$ implies $s x \sim s y$ (`ModuleCon.smul`). The quotient `ModuleCon.Quotient M c` is a module over $S$, by the instance `ModuleCon.instModuleQuotient`, and it is an additive group when $M$ is. The weaker structures are `SMulCon`, which respects the action only, and `VAddCon` for an additive action.

Each map $f$ that respects the action and the sum gives the kernel congruence `ModuleCon.ker f`, with $x \sim y$ if $f(x) = f(y)$. The first isomorphism theorem for congruences is `ModuleCon.quotientKerEquivOfSurjective`: if $f : M \to N$ is a surjective linear map, the quotient by its kernel congruence is linearly equivalent to $N$. A relation $r$ that the action respects generates a module congruence, `SMulCon.addConGen'`. Over a ring, module congruences and submodules carry the same data, so most proofs use the quotient $M / p$ of Section 3.

**Definition (`SModEq`).** For a submodule $U$ of a module $M$ over a ring, the relation `x ≡ y [SMOD U]` holds when $x$ and $y$ have the same image in the quotient $M / U$ of Section 3.

The definition is `SModEq.def`, and `SModEq.sub_mem` gives the usual form $x - y \in U$. The relation is an equivalence relation (`SModEq.refl`, `SModEq.symm`, `SModEq.trans`) that respects sums, negations, differences and scalars (`SModEq.add`, `SModEq.neg`, `SModEq.sub`, `SModEq.smul`), and also finite sums (`SModEq.sum`). It is the equality for $U = \bot$ (`SModEq.bot`) and it always holds for $U = \top$ (`SModEq.top`). It is monotone in $U$ (`SModEq.mono`), and it passes through linear maps (`SModEq.map`, `SModEq.comap`). For an ideal $I$ of a commutative ring, it is the congruence modulo $I$ of number theory: it respects products and powers (`SModEq.mul`, `SModEq.pow`, `SModEq.prod`), and polynomials (`SModEq.eval`). The module `Mathlib.LinearAlgebra.SModEq.Pointwise` describes the cosets: $x + U = y + U$ as sets if and only if `x ≡ y [SMOD U]` (`Submodule.vadd_set_eq_vadd_set_iff`).

**Theorem (`SModEq.pow_pow_add_one`).** Let $I$ be an ideal of a commutative ring $R$ with $p \in I$ for a natural number $p$. If $x \equiv y \pmod I$, then $x^{p^m} \equiv y^{p^m} \pmod{I^{m + 1}}$ for each $m$.

*Proof sketch.* By induction on $m$, it is sufficient to show that $x \equiv y \pmod{I^m}$ with $m \ne 0$ gives $x^p \equiv y^p \pmod{I^{m + 1}}$ (`SModEq.pow_add_one`). Write $y = x + d$ with $d \in I^m$. In the binomial expansion of $(x + d)^p - x^p$, the term $p x^{p-1} d$ is in $I \cdot I^m$, and the other terms have a factor $d^2$, which is in $I^{2m} \subseteq I^{m + 1}$. $\square$

Over $\mathbb{Z}$ with $I = (p)$, this is the classical lemma that $x \equiv y \pmod p$ gives $x^{p^m} \equiv y^{p^m} \pmod{p^{m+1}}$.

The quotient also gives a count. For a submodule $S$ of $M$, `Submodule.card_eq_card_quotient_mul_card` says that $|M| = |S| \cdot |M / S|$, with the cardinality `Nat.card` of Volume 1. This is the theorem of Lagrange for the additive group of $M$.

#### Bimodules

An $(A, B)$-bimodule is an additive group $M$ with a left action of $A$ and a right action of $B$ that commute: $(a m) b = a (m b)$. In Mathlib, a right action of $B$ is a left action of $B^{\mathrm{op}}$, and a bimodule is a module over the tensor product $A \otimes B^{\mathrm{op}}$ over $\mathbb{N}$. The file `Mathlib.Algebra.Module.Bimodule` works with two commuting left actions of $R$-algebras $A$ and $B$, which avoids the opposite ring, so the ring of scalars is `TensorProduct R A B`. A subbimodule is a submodule over the tensor product. The constructor `Subbimodule.mk` builds one from an additive submonoid that is closed under the action of $A$ and of $B$, and `Subbimodule.smul_mem` and `Subbimodule.smul_mem'` are the two closure properties. The maps `Subbimodule.toSubmodule` and `Subbimodule.toSubmodule'` forget to an $A$-submodule and to a $B$-submodule. The maps `Subbimodule.toSubbimoduleInt` and `Subbimodule.toSubbimoduleNat` move between the base rings $\mathbb{N}$ and $\mathbb{Z}$, and `Subbimodule.baseChange` moves between two base rings in general.

#### Graded modules

Let $A = \bigoplus_i A_i$ be a graded ring and $M = \bigoplus_j M_j$, where $\iota_A$ acts on $\iota_B$ by addition. A graded multiplication of $A$ on $M$ is a family of maps $A_i \times M_j \to M_{i + j}$. The class `DirectSum.Gmodule A M` says that this family satisfies the module axioms, and the instance `DirectSum.Gmodule.module` then makes $\bigoplus_j M_j$ a module over $\bigoplus_i A_i$. On homogeneous elements the action is the graded multiplication: `DirectSum.Gmodule.of_smul_of`. The graded ring $A$ is a graded module over itself, by `DirectSum.GSemiring.toGmodule`.

The internal form uses submodules. If $\mathcal{A}$ is a grading of the ring $A$ by additive submonoids and $\mathcal{M}$ is a decomposition of $M$ by submodules with $\mathcal{A}_i \mathcal{M}_j \subseteq \mathcal{M}_{i + j}$, then the instance `SetLike.gmodule` gives the graded module structure, and `GradedModule.linearEquiv` is the $A$-linear equivalence between $M$ and $\bigoplus_j \mathcal{M}_j$. Polynomial rings and their homogeneous submodules are the main example, and Chapter 3 of Volume 8 uses these gradings for tensor algebras.

#### Common errors

1. Using `a • S` or `s • N` without the scope. These two actions are scoped instances and need `open Pointwise`; without it, Lean finds no instance for the action. The sum `p + q` is a global instance and needs no scope, and `Submodule.add_eq_sup` turns it into a join for the lattice lemmas.
2. Expecting `a • S` to be a submodule over $R$ for a noncommutative $R$ and $a \in R$. The map $x \mapsto a x$ is not $R$-linear in general. The pointwise action needs scalars that commute with the $R$-action.
3. Reading `Submodule.map₂ f p q` as the set of the values $f(m, n)$. It is the span of this set, which is larger in general; the set itself is `Set.image2`, and `Submodule.image2_subset_map₂` is the inclusion.

### Exercises

1. (A) In $\mathbb{Q}^2$, compute $p + q$ for the lines $p = \mathbb{Q}(1, 0)$ and $q = \mathbb{Q}(1, 1)$, and check `Submodule.add_eq_sup` on this example.
2. (A) Show that $a \cdot S = S$ for a unit $a$ of a commutative ring $R$ and a submodule $S$.
3. (B) Let $f : \mathbb{Q}^2 \times \mathbb{Q}^2 \to \mathbb{Q}^4$ send $(x, y)$ to $(x_1 y_1, x_1 y_2, x_2 y_1, x_2 y_2)$. Show that the set of the values of $f$ is not a submodule, and find `Submodule.map₂ f ⊤ ⊤`.
4. (B) Let $f : M \to N$ be a surjective linear map over a ring. Show that the kernel congruence of $f$ is the congruence of the submodule $\ker f$.
5. (B) Show that a subbimodule of $A$ as an $(A, A)$-bimodule, for a commutative ring $A$, is an ideal of $A$.
6. (C) Let $A = K[X]$ with the grading $A_i = K X^i$ for $i \in \mathbb{N}$, and let $M = K[X]$ with $M_j = K X^{j - 1}$ for $j \ge 1$ and $M_0 = 0$. Show that $A_i M_j \subseteq M_{i + j}$, so that $M$ is a graded module over $A$ indexed by $\mathbb{N}$.

### Reference

<?reference?>
