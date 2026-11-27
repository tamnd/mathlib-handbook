---
title: Solvable and nilpotent Lie algebras and Engel's theorem
kind: theory
modules:
  - Mathlib.Algebra.Lie.Solvable
  - Mathlib.Algebra.Lie.Nilpotent
  - Mathlib.Algebra.Lie.Engel
  - Mathlib.Algebra.Lie.EngelSubalgebra
  - Mathlib.Algebra.Lie.LieTheorem
  - Mathlib.Algebra.Lie.Character
explains:
  E3: [LieAlgebra.derivedSeriesOfIdeal, LieAlgebra.derivedSeries, LieAlgebra.IsSolvable, LieAlgebra.isSolvable_iff, LieAlgebra.isSolvable_of_isSolvable_ideal_quotient, LieAlgebra.radical, LieModule.lowerCentralSeries, LieModule.IsNilpotent, LieModule.isNilpotent_iff, LieRing.IsNilpotent, LieAlgebra.non_trivial_center_of_isNilpotent, LieModule.isNilpotent_toEnd_of_isNilpotent, LieAlgebra.IsEngelian, LieModule.isNilpotent_iff_forall, LieAlgebra.isNilpotent_iff_forall, LieSubalgebra.engel, LieModule.exists_nontrivial_weightSpace_of_isSolvable, LieAlgebra.LieCharacter, LieAlgebra.lieCharacter_apply_of_mem_derived]
  E2: [LieAlgebra.derivedSeries_def, LieAlgebra.IsSolvable.mk, LieAlgebra.isSolvableAdd, LieAlgebra.radicalIsSolvable, LieAlgebra.LieIdeal.solvable_iff_le_radical, LieAlgebra.center_le_radical, LieAlgebra.derivedLength, LieAlgebra.derivedAbelianOfIdeal, LieAlgebra.abelian_derivedAbelianOfIdeal, Function.Injective.lieAlgebra_isSolvable, Function.Surjective.lieAlgebra_isSolvable, LieAlgebra.ofAbelianIsSolvable, LieAlgebra.isSolvable_of_isNilpotent, LieModule.lowerCentralSeries_succ, LieSubmodule.ucs, LieModule.nontrivial_max_triv_of_isNilpotent, LieModule.exists_forall_pow_toEnd_eq_zero, LieAlgebra.nilpotent_ad_of_nilpotent_algebra, LieAlgebra.isNilpotent_range_ad_iff, LieAlgebra.maxNilpotentIdeal, LieModule.nilpotentOfNilpotentQuotient, LieModule.isNilpotent_quotient_iff, LieAlgebra.isEngelian_of_isNoetherian, LieModule.isNilpotent_iff_forall', LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer, LieSubalgebra.mem_engel_iff, LieSubalgebra.self_mem_engel, LieSubalgebra.normalizer_engel, LieSubalgebra.normalizer_eq_self_of_engel_le, LieSubalgebra.isNilpotent_of_forall_le_engel, LieModule.exists_nontrivial_weightSpace_of_lieIdeal, LieAlgebra.lieCharacter_apply_lie, LieAlgebra.lieCharacterEquivLinearDual]
  E1: auto
families: []
requires: [V07.C05, V09.C03, V29.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Solvable and nilpotent Lie algebras and Engel's theorem

### Overview

Two series of ideals measure how far a Lie algebra is from being abelian. The derived series takes brackets of the previous term with itself, and a Lie algebra is solvable if it ends at $0$. The lower central series takes brackets with the whole algebra, and a Lie algebra is nilpotent if it ends at $0$. The upper triangular matrices are the model of a solvable algebra, and the strictly upper triangular matrices are the model of a nilpotent algebra.

Engel's theorem says that a finite-dimensional Lie algebra is nilpotent if and only if each $\operatorname{ad} x$ is a nilpotent endomorphism. So a condition on single elements controls the whole algebra. Lie's theorem says that, over an algebraically closed field of characteristic $0$, each representation of a solvable algebra has a common eigenvector, so it can be put in upper triangular form. This section proves Engel's theorem in full, states Lie's theorem, and defines the radical, which the next section uses to define semisimple algebras.

In the whole section $R$ is a commutative ring, $L$ is a Lie algebra over $R$ and $M$ is a Lie module over $L$. For the theorems of Engel and Lie, $K$ is a field and all spaces are finite-dimensional.

### Definitions

**Definition (Derived series).** For an ideal $I$ of $L$, the derived series of $I$ is $D^0 I = I$ and $D^{k+1} I = [D^k I, D^k I]$. The derived series of $L$ is $D^k L$, the series of the ideal $L$.

**Definition (Solvable Lie algebra).** The Lie algebra $L$ is solvable if $D^k L = 0$ for some $k$. The least such $k$ is the derived length.

**Definition (Radical).** The radical of $L$ is the sum of all solvable ideals of $L$.

**Definition (Lower central series).** The lower central series of $M$ is $C^0 M = M$ and $C^{k+1} M = [L, C^k M]$. The module $M$ is nilpotent if $C^k M = 0$ for some $k$, and the Lie algebra $L$ is nilpotent if it is nilpotent as a module over itself.

**Definition (Upper central series).** For a Lie submodule $N$ of $M$, the upper central series is $N_0 = N$ and $N_{k+1} = \{m : [x, m] \in N_k \text{ for all } x \in L\}$, the normalizer of $N_k$.

**Definition (Engelian Lie algebra).** The Lie algebra $L$ is Engelian if each Lie module $M$ over $L$ in which every $x \in L$ acts by a nilpotent endomorphism is a nilpotent module.

**Definition (Engel subalgebra).** For $x \in L$, the Engel subalgebra is $E(x) = \{y \in L : (\operatorname{ad} x)^n y = 0 \text{ for some } n\}$, the generalized eigenspace of $\operatorname{ad} x$ for the eigenvalue $0$.

**Definition (Character).** A character of $L$ is a morphism of Lie algebras $\chi : L \to R$, where $R$ is abelian. So $\chi$ is linear and $\chi([x, y]) = 0$ for all $x, y$.

### Theorems and proofs

**Proposition (The derived series).** Each $D^k L$ is an ideal of $L$, and $D^{k+1} L \subseteq D^k L$.

*Proof.* By induction on $k$. If $D^k L$ is an ideal, then $[D^k L, D^k L]$ is an ideal by the proposition on the bracket of ideals in the previous chapter, and it is contained in $D^k L$ by the same proposition. $\square$

The derived series of an ideal $I$ consists of ideals of $L$ by the same argument, so $D^j I$ is an ideal of $L$ for all $j$.

**Theorem (Solvability under morphisms and extensions).** Let $f : L \to L'$ be a morphism.

1. If $f$ is injective and $L'$ is solvable, then $L$ is solvable.
2. If $f$ is surjective and $L$ is solvable, then $L'$ is solvable.
3. If $I$ is an ideal of $L$ and both $I$ and $L / I$ are solvable, then $L$ is solvable.

*Proof.* For each morphism, $f(D^k L) \subseteq D^k L'$ by induction on $k$, because $f([x, y]) = [f x, f y]$. If $f$ is injective and $D^k L' = 0$, then $f(D^k L) = 0$, so $D^k L = 0$. If $f$ is surjective, then $f(D^k L) = D^k L'$ by induction, with the proposition on images of brackets of ideals, so $D^k L = 0$ gives $D^k L' = 0$. For the third claim, let $\pi : L \to L / I$. Then $\pi(D^k L) = D^k(L / I) = 0$ for some $k$, so $D^k L \subseteq I$. By induction on $j$, $D^{k + j} L \subseteq D^j I$, and $D^j I = 0$ for some $j$. $\square$

**Corollary (The radical is solvable).** If $I$ and $J$ are solvable ideals, then $I + J$ is solvable. If $L$ is Noetherian as an $R$-module, then the radical is a solvable ideal, and it is the largest solvable ideal.

*Proof.* The ideal $J$ of $I + J$ is solvable, and $(I + J) / J \cong I / (I \cap J)$ is the image of $I$ under a surjective morphism, so it is solvable. The theorem gives the first claim. If $L$ is Noetherian, then the set of solvable ideals has a maximal element $S$. For each solvable ideal $I$, the ideal $S + I$ is solvable and contains $S$, so $S + I = S$ and $I \subseteq S$. So $S$ is the radical. $\square$

**Proposition (Nilpotent algebras).** Let $L$ be nilpotent with $C^k L = 0$.

1. $D^j L \subseteq C^j L$ for all $j$, so $L$ is solvable.
2. If $L \neq 0$, then the center of $L$ is nonzero.
3. For each $x \in L$, $(\operatorname{ad} x)^k = 0$.

*Proof.* For the first claim, induction: $D^{j+1} L = [D^j L, D^j L] \subseteq [L, C^j L] = C^{j+1} L$. For the second claim, let $m$ be the largest index with $C^m L \neq 0$; it exists because $C^0 L = L \neq 0$. Then $[L, C^m L] = C^{m+1} L = 0$, so $C^m L$ lies in the center. For the third claim, $(\operatorname{ad} x)^j y \in C^j L$ by induction on $j$, because $[x, C^j L] \subseteq C^{j+1} L$. $\square$

**Lemma (ad of a nilpotent endomorphism).** Let $V$ be a module over $R$ and $a \in \operatorname{End}(V)$ with $a^n = 0$. Then $(\operatorname{ad} a)^{2n - 1} = 0$ on $\operatorname{End}(V)$.

*Proof.* Write $\operatorname{ad} a = \lambda - \rho$, with $\lambda(b) = a b$ and $\rho(b) = b a$. The maps $\lambda$ and $\rho$ commute and $\lambda^n = \rho^n = 0$. The binomial formula gives
$$(\lambda - \rho)^{2n - 1} = \sum_{i + j = 2n - 1} \binom{2n-1}{i} (-1)^j \lambda^i \rho^j,$$
and in each term $i \geq n$ or $j \geq n$, so each term is $0$. $\square$

**Theorem (Engel's theorem, linear form).** Let $V \neq 0$ be a finite-dimensional vector space over $K$, and let $L \subseteq \mathfrak{gl}(V)$ be a Lie subalgebra whose elements are all nilpotent endomorphisms. Then there is $v \neq 0$ in $V$ with $x v = 0$ for all $x \in L$.

*Proof.* Induction on $\dim L$, for all $V$ at the same time. If $L = 0$, take any $v \neq 0$. Suppose $L \neq 0$, and let $H$ be a proper subalgebra of $L$ of the largest dimension; $H = 0$ is proper, so $H$ exists.

First, $H$ is an ideal of codimension $1$. The algebra $H$ acts on the space $L / H$ by $h \cdot (y + H) = [h, y] + H$. By the lemma, each $\operatorname{ad} h$ is nilpotent on $\mathfrak{gl}(V)$, so it is nilpotent on $L$ and on $L / H$. The image of $H$ in $\mathfrak{gl}(L / H)$ is a subalgebra of nilpotent endomorphisms of dimension at most $\dim H < \dim L$, and $L / H \neq 0$. By induction there is $y \notin H$ with $[h, y] \in H$ for all $h \in H$. Then $H + K y$ is a subalgebra that contains $H$ strictly, so it is $L$ by the choice of $H$, and $H$ is an ideal of $L$.

Next, let $W = \{v \in V : h v = 0 \text{ for all } h \in H\}$. By induction applied to $H$, $W \neq 0$. For $v \in W$ and $h \in H$,
$$h (y v) = y (h v) + [h, y] v = 0,$$
because $[h, y] \in H$. So $y W \subseteq W$. The restriction of $y$ to $W$ is nilpotent, so it has a nonzero kernel: there is $w \neq 0$ in $W$ with $y w = 0$. Since $L = H + K y$, each element of $L$ kills $w$. $\square$

**Theorem (Engel's theorem).** A finite-dimensional Lie algebra $L$ over $K$ is nilpotent if and only if $\operatorname{ad} x$ is nilpotent for each $x \in L$.

*Proof.* If $L$ is nilpotent, then each $\operatorname{ad} x$ is nilpotent by the proposition on nilpotent algebras. For the converse, use induction on $\dim L$. If $L = 0$ there is nothing to prove. Otherwise, apply the linear form to $\operatorname{ad}(L) \subseteq \mathfrak{gl}(L)$: there is $z \neq 0$ with $[x, z] = 0$ for all $x$, so the center $Z$ of $L$ is nonzero. In $L / Z$ each $\operatorname{ad}(x + Z)$ is nilpotent, because it is induced by $\operatorname{ad} x$, and $\dim L / Z < \dim L$. By induction $C^k(L / Z) = 0$ for some $k$, so $C^k L \subseteq Z$, and $C^{k+1} L = [L, C^k L] \subseteq [L, Z] = 0$. $\square$

**Theorem (Lie's theorem).** Let $K$ be an algebraically closed field of characteristic $0$, let $L$ be a solvable Lie algebra over $K$, and let $V \neq 0$ be a finite-dimensional Lie module over $L$. Then there is a linear form $\chi : L \to K$ and $v \neq 0$ in $V$ with $x v = \chi(x) v$ for all $x \in L$.

The proof uses an ideal $A$ of codimension $1$, which exists because $[L, L] \neq L$, a common eigenvector of $A$ by induction, and the invariance lemma: the weight space of $A$ for a weight $\lambda$ is stable under $L$. The invariance lemma needs characteristic $0$, through the fact that a trace $n \lambda([x, a])$ vanishes only if $\lambda([x, a]) = 0$. By induction on $\dim V$, Lie's theorem gives a basis in which $L$ acts by upper triangular matrices.

**Proposition (Characters).** Each character $\chi$ vanishes on $[L, L]$. If $L$ is abelian, then the characters of $L$ are exactly the linear forms on $L$.

*Proof.* The ideal $[L, L]$ is spanned by brackets, and $\chi([x, y]) = [\chi x, \chi y] = 0$ in the abelian algebra $R$. If $L$ is abelian, then both sides of $\chi([x, y]) = [\chi x, \chi y]$ are $0$ for each linear form, so each linear form is a character. $\square$

### Examples

**Example (Triangular matrices).** Let $\mathfrak{t}_n \subseteq \mathfrak{gl}_n(K)$ be the upper triangular matrices and $\mathfrak{n}_n$ the strictly upper triangular ones. Write $\mathfrak{n}_n^{(r)}$ for the matrices with $a_{ij} = 0$ when $j - i < r$. A product of an element of $\mathfrak{n}_n^{(r)}$ and an element of $\mathfrak{n}_n^{(s)}$ lies in $\mathfrak{n}_n^{(r+s)}$, so $C^k \mathfrak{n}_n \subseteq \mathfrak{n}_n^{(k+1)}$, which is $0$ for $k \geq n - 1$. So $\mathfrak{n}_n$ is nilpotent. The diagonal of $[x, y]$ for $x, y \in \mathfrak{t}_n$ is $0$, so $[\mathfrak{t}_n, \mathfrak{t}_n] \subseteq \mathfrak{n}_n$, and $\mathfrak{t}_n$ is solvable. Lie's theorem says that each solvable subalgebra of $\mathfrak{gl}(V)$ over an algebraically closed field of characteristic $0$ is contained in some $\mathfrak{t}_n$ after a change of basis.

**Example (Solvable but not nilpotent).** Let $L$ have basis $x, y$ with $[x, y] = y$. Then $D^1 L = K y$ and $D^2 L = 0$, so $L$ is solvable. But $C^1 L = K y$ and $C^2 L = [L, K y] = K y$, so $C^k L = K y$ for all $k \geq 1$, and $L$ is not nilpotent. Here $\operatorname{ad} y$ is nilpotent, but $\operatorname{ad} x$ has the eigenvalue $1$ on $y$. So Engel's theorem needs the condition for each element.

**Example (sl2 is not solvable).** In $\mathfrak{sl}_2(K)$ with characteristic not $2$, $[e, f] = h$, $[h, e] = 2 e$ and $[h, f] = -2 f$, so $[\mathfrak{sl}_2, \mathfrak{sl}_2] = \mathfrak{sl}_2$ and $D^k \mathfrak{sl}_2 = \mathfrak{sl}_2$ for all $k$. The elements $e$ and $f$ have nilpotent $\operatorname{ad}$, but $h$ does not.

**Counterexample (Lie's theorem in characteristic p).** Let $K$ have characteristic $p > 0$, and let $L$ be the algebra with $[x, y] = y$. On $V = K^p$ with basis $v_0, \dots, v_{p-1}$, let $x v_i = i v_i$ and $y v_i = v_{i+1}$, with indices mod $p$. Then $[x, y] v_i = (i + 1) v_{i+1} - i v_{i+1} = y v_i$, so $V$ is a Lie module. Since $(y - 1)^p = y^p - 1 = 0$ and $y - 1$ has rank $p - 1$, the only eigenvectors of $y$ are the multiples of $\sum_i v_i$. This vector is not an eigenvector of $x$, since $x \sum_i v_i = \sum_i i v_i$. So the solvable algebra $L$ has no common eigenvector, and the same holds over the algebraic closure of $K$.

### The library around it

::: mathlib
`LieAlgebra.IsSolvable` · `Mathlib.Algebra.Lie.Solvable`

`LieAlgebra.derivedSeriesOfIdeal R L k I` is the series of an ideal, and `derivedSeries R L k` is an abbreviation for the series of `⊤`, with `derivedSeries_def`. The class `LieAlgebra.IsSolvable L` takes only `[LieRing L]` and is stated over `ℤ`; `isSolvable_iff R L` gives the form over `R`. The closure facts are `Function.Injective.lieAlgebra_isSolvable`, `Function.Surjective.lieAlgebra_isSolvable` and `isSolvable_of_isSolvable_ideal_quotient`, with the instances `isSolvableAdd`, `ofAbelianIsSolvable` and `isSolvable_of_isNilpotent` (in `Mathlib.Algebra.Lie.Nilpotent`). `derivedLength` is the length, and `derivedAbelianOfIdeal I` is the last nonzero term, abelian by `abelian_derivedAbelianOfIdeal`.

<?decl LieAlgebra.IsSolvable?>
:::

::: mathlib
`LieAlgebra.radical` · `Mathlib.Algebra.Lie.Solvable`

`LieAlgebra.radical R L` is the supremum of the solvable ideals. The instance `radicalIsSolvable` needs `[IsNoetherian R L]`, and `LieAlgebra.LieIdeal.solvable_iff_le_radical` is the maximality, with `center_le_radical`.

<?decl LieAlgebra.radical?>
:::

::: mathlib
`LieModule.IsNilpotent` · `Mathlib.Algebra.Lie.Nilpotent`

`LieModule.lowerCentralSeries R L M k` has `lowerCentralSeries_succ : … (k + 1) = ⁅⊤, … k⁆`. The class `LieModule.IsNilpotent L M` is stated over `ℤ`, and `isNilpotent_iff R L M` is the form over `R`. `LieRing.IsNilpotent L` is an abbreviation for the module `L` over itself. `LieAlgebra.non_trivial_center_of_isNilpotent` and `LieModule.nontrivial_max_triv_of_isNilpotent` give the nonzero center and the nonzero invariants, and `isNilpotent_toEnd_of_isNilpotent`, `exists_forall_pow_toEnd_eq_zero` and `LieAlgebra.nilpotent_ad_of_nilpotent_algebra` are the nilpotency of the action. `LieSubmodule.ucs` is the upper central series, and `nilpotentOfNilpotentQuotient` and `isNilpotent_quotient_iff` treat quotients. `LieAlgebra.maxNilpotentIdeal` is the largest nilpotent ideal.

<?decl LieModule.IsNilpotent?>
:::

::: mathlib
`LieModule.isNilpotent_iff_forall` · `Mathlib.Algebra.Lie.Engel`

The library proves Engel's theorem over any commutative ring. `LieAlgebra.IsEngelian R L` is the property of the definition, and `isEngelian_of_isNoetherian` proves it for each Noetherian `L` with a maximal Engelian subalgebra, which can be enlarged by `exists_engelian_lieSubalgebra_of_lt_normalizer` while it is not self-normalizing. `LieModule.isNilpotent_iff_forall` (under `[IsNoetherian R L]`) and `isNilpotent_iff_forall'` (under `[IsNoetherian R M]`) state that `M` is nilpotent if and only if each `toEnd x` is nilpotent, and `LieAlgebra.isNilpotent_iff_forall` is the case `M = L`. The linear form of the text follows with `nontrivial_max_triv_of_isNilpotent`.

<?decl LieModule.isNilpotent_iff_forall?>
:::

::: mathlib
`LieSubalgebra.engel` · `Mathlib.Algebra.Lie.EngelSubalgebra`

`LieSubalgebra.engel R x` has `mem_engel_iff : y ∈ engel R x ↔ ∃ n, (ad R L x ^ n) y = 0` and `self_mem_engel`. `normalizer_engel` states that it is self-normalizing, `normalizer_eq_self_of_engel_le` (under `[IsArtinian R L]`) extends this to each subalgebra that contains an Engel subalgebra, and `isNilpotent_of_forall_le_engel` gives nilpotency. These facts lead to the Cartan subalgebras of the next chapter.

<?decl LieSubalgebra.engel?>
:::

::: mathlib
`LieModule.exists_nontrivial_weightSpace_of_isSolvable` · `Mathlib.Algebra.Lie.LieTheorem`

Lie's theorem is `exists_nontrivial_weightSpace_of_isSolvable k L V`: for a field `k` with `[CharZero k]`, `[Module.Finite k V]`, `[Nontrivial V]`, `[IsSolvable L]` and `[LieModule.IsTriangularizable k L V]`, there is `χ : Module.Dual k L` with `Nontrivial (weightSpace V χ)`. The class `IsTriangularizable` asks that each `toEnd x` has all its eigenvalues in `k`; it holds over an algebraically closed field by `LieModule.instIsTriangularizableOfIsAlgClosed`. The inductive step is `exists_nontrivial_weightSpace_of_lieIdeal`. For nilpotent algebras, the version in any characteristic is `LieModule.exists_nontrivial_weightSpace_of_isNilpotent`. The index of this edition has no declaration for the flag form of Lie's theorem.

<?decl LieModule.exists_nontrivial_weightSpace_of_isSolvable?>
:::

::: mathlib
`LieAlgebra.LieCharacter` · `Mathlib.Algebra.Lie.Character`

`LieAlgebra.LieCharacter R L` is an abbreviation for `L →ₗ⁅R⁆ R`. `lieCharacter_apply_lie` gives $\chi([x, y]) = 0$, `lieCharacter_apply_of_mem_derived` the vanishing on `derivedSeries R L 1`, and `lieCharacterEquivLinearDual` the bijection with `Module.Dual R L` for an abelian `L`.

<?decl LieAlgebra.LieCharacter?>
:::

Common errors of a learner: The first error is to give `R` to `LieAlgebra.IsSolvable` or `LieModule.IsNilpotent`; both classes are stated over `ℤ` and take no ring, and `isSolvable_iff R L` and `isNilpotent_iff R L M` connect them with the series over `R`. The second error is to expect the radical to be solvable without `[IsNoetherian R L]`. The third error is to search for Lie's theorem as a statement about a flag; the library states it as the existence of a nonzero weight space, and the hypothesis `IsTriangularizable` replaces an algebraically closed field.

### Exercises

1. (A) Show that a subalgebra and a quotient of a nilpotent Lie algebra are nilpotent, and that $\mathfrak{t}_n / \mathfrak{n}_n$ is abelian. Hint: $f(C^k L) = C^k L'$ for a surjective morphism.
2. (A) Show that the Heisenberg algebra with $[x, y] = z$ is nilpotent but not abelian, and find its center. Hint: $C^1 = K z$ and $C^2 = 0$.
3. (A) Show that if $L / Z(L)$ is nilpotent, then $L$ is nilpotent, and give an example where $L / I$ and $I$ are nilpotent but $L$ is not. Hint: for the example, take $[x, y] = y$ and $I = K y$.
4. (B) Show that $\mathfrak{n}_n$ satisfies $D^k \mathfrak{n}_n \subseteq \mathfrak{n}_n^{(2^k)}$, and find the derived length of $\mathfrak{n}_3$. Hint: $[\mathfrak{n}^{(r)}, \mathfrak{n}^{(r)}] \subseteq \mathfrak{n}^{(2r)}$.
5. (B) Show that each nilpotent Lie algebra $L \neq 0$ has an ideal of codimension $1$. Hint: if $[L, L] = L$, then $C^k L = L$ for all $k$; each subspace that contains $[L, L]$ is an ideal.
6. (C) Use the linear form of Engel's theorem to show that a Lie subalgebra $L \subseteq \mathfrak{gl}(V)$ of nilpotent endomorphisms is conjugate to a subalgebra of $\mathfrak{n}_n$, $n = \dim V$. Hint: induction on $\dim V$, with the quotient $V / K v$ for a common null vector $v$.

### Notes and history

The theorem on nilpotent algebras carries the name of Friedrich Engel, who worked with Lie on the theory of transformation groups, and the triangular form of solvable algebras over the complex numbers carries the name of Lie. The source of `Mathlib.Algebra.Lie.Engel` cites a proof by Zorn from 1937 of Engel's theorem for general coefficients, and the library proof with a maximal Engelian subalgebra follows that line instead of the induction on dimension of the text.

The Mathlib files are by these authors, read from their headers: `Solvable`, `Nilpotent`, `Engel` and `Character` (all under `Mathlib.Algebra.Lie`) by Oliver Nash; `EngelSubalgebra` by Johan Commelin; and `LieTheorem` by Lucas Whitfield and Johan Commelin.

### Reference

<?reference?>
