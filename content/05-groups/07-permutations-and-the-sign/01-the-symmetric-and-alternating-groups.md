---
title: Transpositions, the sign and the alternating group
kind: theory
modules:
  - Mathlib.GroupTheory.Perm.Sign
  - Mathlib.GroupTheory.SpecificGroups.Alternating
  - Mathlib.GroupTheory.Perm.Basic
  - Mathlib.GroupTheory.Perm.Subgroup
explains:
  E3: [Equiv.Perm.sign]
  E2: [Equiv.Perm.sign_swap, Equiv.Perm.sign_mul, Equiv.Perm.signAux, Equiv.Perm.swap_induction_on, Equiv.Perm.closure_isSwap, Equiv.Perm.sign_surjective, alternatingGroup, Equiv.Perm.mem_alternatingGroup, alternatingGroup.index_eq_two, two_mul_card_alternatingGroup]
  E1: auto
families: []
requires: [V05.C05]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V05/C07/Examples.lean
  - MathlibHandbook/V05/C07/Exercises.lean
  - MathlibHandbook/V05/C07/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Transpositions, the sign and the alternating group

### Overview

The symmetric group $S_n$ is the group of all the permutations of $\{1, \ldots, n\}$. By Cayley's theorem each finite group is a subgroup of some $S_n$, so the symmetric groups contain all finite groups. The simplest permutations are the transpositions, which exchange two points. Each permutation is a product of transpositions, in many ways. But the parity of the number of factors does not depend on the choice. This parity gives the sign, a surjective homomorphism $S_n \to \{\pm 1\}$ for $n \ge 2$. Its kernel is the alternating group $A_n$, a normal subgroup of index $2$.

The well-definedness of the sign is a real theorem, and this section proves it with the count of inversions. The next section decomposes permutations into cycles and describes conjugacy in $S_n$. Volume 6 uses the sign to define the determinant.

### Definitions

**Definition (Symmetric group).** For a set $X$, $\operatorname{Sym}(X)$ is the group of the bijections $X \to X$ under composition. For $X = \{1, \ldots, n\}$ it is $S_n$. A product $\sigma \tau$ means: apply $\tau$ first, then $\sigma$.

In Mathlib the group is `Equiv.Perm X`, the type `X ≃ X`, and the product is `σ * τ = τ.trans σ`, so `(σ * τ) x = σ (τ x)`. The order of `Equiv.Perm (Fin n)` is `n !`, by `Fintype.card_perm`.

**Definition (Transposition).** For $a \ne b$ in $X$, the transposition $(a\,b)$ exchanges $a$ and $b$ and fixes the other points. It is `Equiv.swap a b`, and the property of being a transposition is `Equiv.Perm.IsSwap`.

**Definition (Inversion).** Let $\sigma \in S_n$. An inversion of $\sigma$ is a pair $i < j$ with $\sigma(i) > \sigma(j)$. Let $\operatorname{inv}(\sigma)$ be the number of inversions.

**Definition (Sign).** The sign of $\sigma \in S_n$ is $\operatorname{sgn}(\sigma) = (-1)^{\operatorname{inv}(\sigma)}$. The permutation is even if $\operatorname{sgn}(\sigma) = 1$ and odd if $\operatorname{sgn}(\sigma) = -1$.

::: mathlib
`Equiv.Perm.signAux` · `Mathlib.GroupTheory.Perm.Sign`

The sign by inversions, for permutations of `Fin n`: a product over the pairs, with a factor `-1` for each inversion. It is an auxiliary definition. The sign of a permutation of an arbitrary finite type is defined from it by a choice of a bijection with `Fin n`, and the proof that the choice does not matter is the multiplicativity below.

<?decl Equiv.Perm.signAux?>
:::

::: mathlib
`Equiv.Perm.sign` · `Mathlib.GroupTheory.Perm.Sign`

The sign as a bundled homomorphism `Perm α →* ℤˣ`, for a finite type `α` with decidable equality. The value is in the group of units of `ℤ`, which is $\{1, -1\}$. The theorems of this section are built into the type: it is a homomorphism.

<?decl Equiv.Perm.sign?>
:::

### Theorems and proofs

**Theorem (Product formula).** For $\sigma \in S_n$,
$$\operatorname{sgn}(\sigma) = \prod_{1 \le i < j \le n} \frac{\sigma(j) - \sigma(i)}{j - i}.$$

*Proof.* Let $P$ be the product on the right. For each pair $i < j$, the factor is negative if and only if $(i, j)$ is an inversion. So the sign of $P$ is $(-1)^{\operatorname{inv}(\sigma)}$. The absolute value of $P$ is $1$: the map $\{i, j\} \mapsto \{\sigma(i), \sigma(j)\}$ is a bijection on the set of the pairs, so the numbers $|\sigma(j) - \sigma(i)|$ are the numbers $|j - i|$ in another order. $\square$

**Theorem (The sign is a homomorphism).** For $\sigma, \tau \in S_n$, $\operatorname{sgn}(\sigma \tau) = \operatorname{sgn}(\sigma) \operatorname{sgn}(\tau)$.

*Proof.* For a pair $i \ne j$ the quotient $\frac{f(j) - f(i)}{j - i}$ does not change when $i$ and $j$ are exchanged, so it is a function of the unordered pair $\{i, j\}$. Write the product formula over unordered pairs. Then
$$\operatorname{sgn}(\sigma \tau) = \prod_{\{i, j\}} \frac{\sigma(\tau(j)) - \sigma(\tau(i))}{\tau(j) - \tau(i)} \cdot \prod_{\{i, j\}} \frac{\tau(j) - \tau(i)}{j - i}.$$
The factors $\tau(j) - \tau(i)$ are not zero, since $\tau$ is injective. The second product is $\operatorname{sgn}(\tau)$. In the first product, put $\{k, l\} = \{\tau(i), \tau(j)\}$. As $\{i, j\}$ runs over all the unordered pairs, so does $\{k, l\}$, because $\tau$ is a bijection. So the first product is $\prod_{\{k, l\}} \frac{\sigma(l) - \sigma(k)}{l - k} = \operatorname{sgn}(\sigma)$. $\square$

::: mathlib
`Equiv.Perm.sign_mul` · `Mathlib.GroupTheory.Perm.Sign`

The theorem `sign (σ * τ) = sign σ * sign τ`, which is `map_mul` for the bundled `sign`. The consequences `Equiv.Perm.sign_one` and `Equiv.Perm.sign_inv` are the general facts of Chapter 2.

<?decl Equiv.Perm.sign_mul?>
:::

**Theorem (Sign of a transposition).** Each transposition is odd.

*Proof.* Let $a < b$ and $\tau = (a\,b)$. Count the inversions $(i, j)$ with $i < j$. If neither $i$ nor $j$ is in $\{a, b\}$, then $\tau$ fixes both and the pair is not an inversion. The pair $(a, b)$ is an inversion. For $m$ with $a < m < b$, both pairs $(a, m)$ and $(m, b)$ are inversions, since $\tau(a) = b > m$ and $m > a = \tau(b)$. For $m < a$ or $m > b$, the pairs with $a$ or $b$ keep their order, since $\tau(a)$ and $\tau(b)$ are on the same side of $m$. So $\operatorname{inv}(\tau) = 1 + 2(b - a - 1)$, which is odd. $\square$

::: mathlib
`Equiv.Perm.sign_swap` · `Mathlib.GroupTheory.Perm.Sign`

The theorem `x ≠ y → sign (swap x y) = -1`. The hypothesis is needed: `swap x x` is the identity, of sign `1`.

<?decl Equiv.Perm.sign_swap?>
:::

**Theorem (Products of transpositions).** For $n \ge 2$, each $\sigma \in S_n$ is a product of transpositions. The identity is the empty product.

*Proof.* Induction on $n$. For $n = 1$ the only permutation is the identity. Let $n \ge 2$ and $\sigma \in S_n$. If $\sigma(n) = n$, let $\rho = \sigma$. Otherwise let $\rho = (n\,\sigma(n)) \sigma$. In both cases $\rho(n) = n$. So $\rho$ is a permutation of $\{1, \ldots, n - 1\}$, and it is a product of transpositions by the hypothesis of induction. Then $\sigma = \rho$ or $\sigma = (n\,\sigma(n)) \rho$, since a transposition is its own inverse. $\square$

::: mathlib
`Equiv.Perm.swap_induction_on` · `Mathlib.GroupTheory.Perm.Sign`

The induction principle that the theorem gives: a property that holds for `1` and passes from `f` to `swap x y * f` for `x ≠ y` holds for each permutation of a finite type.

<?decl Equiv.Perm.swap_induction_on?>
:::

::: mathlib
`Equiv.Perm.closure_isSwap` · `Mathlib.GroupTheory.Perm.Sign`

The theorem as a statement about subgroups: the closure of the set of transpositions is `⊤`.

<?decl Equiv.Perm.closure_isSwap?>
:::

**Corollary (Parity).** If $\sigma$ is a product of $k$ transpositions, then $\operatorname{sgn}(\sigma) = (-1)^k$. So no permutation is both a product of an even number and of an odd number of transpositions.

*Proof.* Apply the homomorphism property $k - 1$ times and the sign of a transposition. $\square$

**Definition (Alternating group).** The alternating group $A_n$ is the kernel of $\operatorname{sgn}$, the group of the even permutations.

::: mathlib
`alternatingGroup` · `Mathlib.GroupTheory.SpecificGroups.Alternating`

The subgroup `alternatingGroup α := sign.ker` of `Perm α`. It is normal by the instance `alternatingGroup.normal`.

<?decl alternatingGroup?>
:::

::: mathlib
`Equiv.Perm.mem_alternatingGroup` · `Mathlib.GroupTheory.SpecificGroups.Alternating`

The membership `σ ∈ alternatingGroup α ↔ sign σ = 1`.

<?decl Equiv.Perm.mem_alternatingGroup?>
:::

**Theorem (The alternating group).** For $n \ge 2$, the sign is onto $\{\pm 1\}$, $A_n$ is a normal subgroup of index $2$, and $|A_n| = n!/2$. The odd permutations form the coset $(1\,2) A_n$.

*Proof.* The sign of $(1\,2)$ is $-1$ and the sign of the identity is $1$, so the sign is onto. By the first isomorphism theorem, $S_n / A_n \cong \{\pm 1\}$, which has two elements. So $[S_n : A_n] = 2$ and $|A_n| = n!/2$ by Lagrange's theorem. A kernel is normal. The coset $(1\,2) A_n$ is not $A_n$, so it is the other coset, the set of the odd permutations. $\square$

::: mathlib
`Equiv.Perm.sign_surjective` · `Mathlib.GroupTheory.Perm.Sign`

The sign is surjective when `1 < Fintype.card α`. For a type with one element, each permutation is the identity, and the sign takes only the value `1`.

<?decl Equiv.Perm.sign_surjective?>
:::

::: mathlib
`alternatingGroup.index_eq_two` · `Mathlib.GroupTheory.SpecificGroups.Alternating`

The index `(alternatingGroup α).index = 2`, under the hypothesis `Nontrivial α`.

<?decl alternatingGroup.index_eq_two?>
:::

::: mathlib
`two_mul_card_alternatingGroup` · `Mathlib.GroupTheory.SpecificGroups.Alternating`

The count `2 * card (alternatingGroup α) = card (Perm α)` for a nontrivial finite type. The version that divides is `card_alternatingGroup`.

<?decl two_mul_card_alternatingGroup?>
:::

### Examples

**Example (Signs in $S_3$).** The permutation $\sigma = (1\,2\,3)$ sends $1 \mapsto 2$, $2 \mapsto 3$, $3 \mapsto 1$. In one-line form it is $2\,3\,1$. Its inversions are $(1, 3)$ and $(2, 3)$, since $\sigma(1) = 2 > 1 = \sigma(3)$ and $\sigma(2) = 3 > 1 = \sigma(3)$. So $\operatorname{sgn}(\sigma) = 1$. Indeed $(1\,2\,3) = (1\,3)(1\,2)$, a product of two transpositions. So $A_3 = \{e, (1\,2\,3), (1\,3\,2)\}$, and the three transpositions are odd.

**Example (The elements of $A_4$).** The group $A_4$ has $12$ elements: the identity, the three products $(1\,2)(3\,4)$, $(1\,3)(2\,4)$, $(1\,4)(2\,3)$, and the eight $3$-cycles. Each $3$-cycle $(a\,b\,c) = (a\,c)(a\,b)$ is even. A $4$-cycle $(a\,b\,c\,d) = (a\,d)(a\,c)(a\,b)$ is odd, and so is a transposition. The count $1 + 3 + 8 = 12 = 4!/2$ agrees with the theorem.

**Counterexample (The factorization is not unique).** The $3$-cycle $(1\,2\,3)$ is $(1\,3)(1\,2)$ and also $(1\,2)(2\,3)$: the second product sends $3 \mapsto 2 \mapsto 1$, $1 \mapsto 2$, and $2 \mapsto 3$. It is also $(1\,3)(1\,2)(2\,3)(2\,3)$, with four factors. The factors and their number change, and only the parity is fixed. So a definition of the sign as "$(-1)^{\text{number of factors}}$" needs the theorem of this section to be a definition at all.

**Example (The fifteen puzzle).** In the $4 \times 4$ sliding puzzle, label the cells $1$ to $16$ and the blank $16$. A move exchanges the blank with a neighbour, which is a transposition of the $16$ labels. Colour the cells like a chess board. Each move changes the colour of the cell of the blank. If the blank starts and ends in the corner, the number of moves is even, so the final arrangement is an even permutation. The arrangement with $14$ and $15$ exchanged is the odd permutation $(14\,15)$. So no sequence of moves reaches it.

**Example (Permutations in Lean).**

<?lean MathlibHandbook/V05/C07/Examples.lean#perm?>

**Example (Transpositions in Lean).**

<?lean MathlibHandbook/V05/C07/Examples.lean#swap?>

**Example (The sign of a transposition in Lean).**

<?lean MathlibHandbook/V05/C07/Examples.lean#sign_swap?>

**Example (The sign is a homomorphism in Lean).**

<?lean MathlibHandbook/V05/C07/Examples.lean#sign_mul?>

**Example (The index of the alternating group in Lean).**

<?lean MathlibHandbook/V05/C07/Examples.lean#alternating?>

### The library around it

The sign is in `Mathlib.GroupTheory.Perm.Sign`, with `Equiv.Perm.sign_symm_trans_trans`, the invariance of the sign under a change of the labels, and `Equiv.Perm.truncSwapFactors`, a computable list of transpositions with product `σ`. The determinant of Volume 6 is a sum over `Equiv.Perm n` with the factor `sign σ`. The group `alternatingGroup (Fin n)` is simple for $n \ge 5$, by `alternatingGroup.isSimpleGroup`, which is the group theoretic core of the theorem of Abel and Ruffini.

The module `Mathlib.GroupTheory.Perm.Subgroup` holds Cayley's theorem in the form `Equiv.Perm.subgroupOfMulAction`: a group that acts faithfully on $H$ is isomorphic to its image in `Equiv.Perm H`. With the action of $G$ on itself, each group is a subgroup of a symmetric group. The module also counts the images of the block embeddings: `Equiv.Perm.sumCongrHom.card_range` gives $|S_\alpha \times S_\beta|$ for the permutations of $\alpha \oplus \beta$ that preserve the two parts, and `Equiv.Perm.subtypeCongrHom.card_range` does the same for a set and its complement. The small module `Mathlib.GroupTheory.Perm.Basic` says that the powers and the inverse of a permutation that maps a set $s$ bijectively onto itself do the same (`Set.BijOn.perm_pow`, `Set.BijOn.perm_zpow`, `Set.BijOn.perm_inv`), and that a transposition acts as an involution in each action of `Equiv.Perm α` (`Equiv.swap_smul_involutive`).

Common errors of a learner:

- The product in `Equiv.Perm` composes from right to left: `(σ * τ) x = σ (τ x)`. Some books use the other order, and their tables of products differ.
- `Equiv.Perm.sign` takes values in `ℤˣ`, not in `ℤ`. A coercion `((sign σ : ℤˣ) : ℤ)` is needed to use the sign as a number.
- `sign` needs `[DecidableEq α] [Fintype α]`. Two different instances of `Fintype α` give the same sign, but the terms differ, and `convert` may be needed.

### Exercises

1. (A) Find the sign of the permutation $3\,1\,4\,2$ (one-line form) by counting inversions, and write it as a product of transpositions.
2. (A) Show that a $k$-cycle $(a_1\,a_2\,\cdots\,a_k)$ has sign $(-1)^{k - 1}$.
3. (B) Show that $\operatorname{inv}(\sigma)$ is the least number of transpositions of adjacent numbers $(i\,i{+}1)$ whose product is $\sigma$.
4. (B) Show that each subgroup $H \le S_n$ that is not inside $A_n$ has exactly half of its elements in $A_n$. Hint: use the second isomorphism theorem, or the coset of an odd element.
5. (L) Prove that a transposition of `Fin 4` is its own inverse. The solution is `swap_mul_self_example`.
6. (L) Prove that $\sigma$ and $\sigma^{-1}$ have the same sign. The solution is `sign_inv_example`.
7. (L) Prove that a product of two transpositions of `Fin 4` is in $A_4$. The solution is `mem_alternating_example`.
8. (L) Prove that $A_4$ has $12$ elements. The solution is `card_alternating_example`.
9. (C) Show that the sign is the only surjective homomorphism $S_n \to \{\pm 1\}$. Hint: all transpositions are conjugate, so they have the same image.

### Notes and history

Cramer used the parity of a permutation in 1750 to state his rule for linear equations, and Vandermonde and Laplace used it in their work on determinants. Cauchy proved in 1815 that the parity is well defined, and he introduced the notation of cycles. The fifteen puzzle was a craze in 1880, and Johnson and Story proved in 1879 that exactly half of the positions can be reached.

In Mathlib the sign is first defined on `Fin n` by inversions and then moved to each finite type. The proof that the result does not depend on the bijection with `Fin n` uses the multiplicativity, and the final term is computable because the bijection is taken through a `Trunc`.

### Reference

<?reference?>
