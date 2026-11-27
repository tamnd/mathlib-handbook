---
title: The Killing form and semisimple Lie algebras
kind: theory
modules:
  - Mathlib.Algebra.Lie.TraceForm
  - Mathlib.Algebra.Lie.Killing
  - Mathlib.Algebra.Lie.InvariantForm
  - Mathlib.Algebra.Lie.Semisimple.Defs
  - Mathlib.Algebra.Lie.Semisimple.Basic
  - Mathlib.Algebra.Lie.Semisimple.Lemmas
  - Mathlib.Algebra.Lie.CartanCriterion
  - Mathlib.Algebra.Lie.Derivation.Killing
  - Mathlib.Algebra.Lie.AdjointAction.JordanChevalley
explains:
  E3: [LieModule.traceForm, killingForm, LieModule.traceForm_isSymm, LieModule.traceForm_apply_lie_apply, LinearMap.BilinForm.lieInvariant, LieIdeal.killingCompl, LieIdeal.killingForm_eq, LieModule.traceForm_eq_zero_of_isNilpotent, LieIdeal.le_killingCompl_top_of_isLieAbelian, LieAlgebra.IsSimple, LieAlgebra.IsSemisimple, LieAlgebra.HasTrivialRadical, LieAlgebra.IsKilling, LieIdeal.isCompl_killingCompl, LieAlgebra.IsKilling.instSemisimple, LieAlgebra.isSolvable_of_killingForm_apply_lie_eq_zero, LieAlgebra.HasTrivialRadical.instIsKilling, LieAlgebra.hasTrivialRadical_iff_isKilling, LieDerivation.IsKilling.exists_eq_ad]
  E2: [killingForm_apply_apply, LieModule.traceForm_apply_apply, LieModule.traceForm_lieInvariant, LieIdeal.restrict_killingForm, LieIdeal.mem_killingCompl, LieAlgebra.InvariantForm.orthogonal, LieAlgebra.InvariantForm.orthogonal_isCompl, LieAlgebra.InvariantForm.isSemisimple_of_nondegenerate, LieAlgebra.HasCentralRadical, LieAlgebra.IsSemisimple.isSimple_of_isAtom, LieAlgebra.IsSemisimple.instHasTrivialRadical, LieAlgebra.IsSimple.instIsSemisimple, LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals, LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals, LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful, LieAlgebra.trace_toEnd_eq_zero, LieAlgebra.ad_ker_eq_bot_of_hasTrivialRadical, LieAlgebra.IsKilling.killingCompl_top_eq_bot, LieAlgebra.IsKilling.killingForm_nondegenerate, LieAlgebra.IsKilling.instHasTrivialRadical, LieAlgebra.IsKilling.ideal_eq_bot_of_isLieAbelian, LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero, LieAlgebra.killingCompl_top_le_radical, LieIdeal.isSolvable_of_killingForm_apply_lie_eq_zero, LieDerivation.IsKilling.range_ad_eq_top, LieDerivation.IsKilling.ad_mem_orthogonal_of_mem_orthogonal, LieAlgebra.ad_mem_adjoin_of_isSemisimple, LieAlgebra.ad_mem_adjoin_of_isNilpotent]
  E1: auto
families: []
requires: [V07.C05, V08.C05, V29.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Killing form and semisimple Lie algebras

### Overview

The Killing form of a Lie algebra $L$ is the bilinear form $\kappa(x, y) = \operatorname{tr}(\operatorname{ad} x \circ \operatorname{ad} y)$. It is symmetric and invariant, $\kappa([x, y], z) = \kappa(x, [y, z])$, and it detects the structure of $L$. Cartan's two criteria, for a finite-dimensional algebra over a field of characteristic $0$, say that $L$ is solvable if and only if $\kappa(L, [L, L]) = 0$, and that $L$ is semisimple if and only if $\kappa$ is non-degenerate.

A semisimple Lie algebra has no nonzero solvable ideal. With a non-degenerate Killing form, each ideal has a complement, the semisimple algebra is the direct sum of its simple ideals, and each derivation is inner. This section proves these facts, computes the Killing form of $\mathfrak{sl}_2$, and explains the three notions of semisimplicity in the library.

In the whole section $R$ is a commutative ring, $K$ is a field, $L$ is a Lie algebra and $M$ is a Lie module over $L$, all free and finite over the ring of scalars when a trace is taken.

### Definitions

**Definition (Trace form and Killing form).** The trace form of $M$ is the bilinear form on $L$
$$B_M(x, y) = \operatorname{tr}_M(\varphi(x) \circ \varphi(y)),$$
where $\varphi : L \to \operatorname{End}(M)$ is the action. The Killing form is $\kappa = B_L$, the trace form of the adjoint representation.

**Definition (Invariant form).** A bilinear form $B$ on a Lie module $M$ is invariant if $B([x, m], n) = -B(m, [x, n])$ for all $x \in L$ and $m, n \in M$. For $M = L$ this is $B([x, y], z) = B(x, [y, z])$.

**Definition (Killing orthogonal).** For an ideal $I$, the Killing orthogonal is $I^\perp = \{x \in L : \kappa(x, i) = 0 \text{ for all } i \in I\}$. The ideal $L^\perp$ is the kernel of the Killing form.

**Definition (Simple and semisimple).** A Lie algebra $L$ is simple if it is not abelian and its only ideals are $0$ and $L$. It is semisimple if it is the direct sum of the minimal nonzero ideals and none of these is abelian. It has trivial radical if its radical is $0$, that is, if $0$ is its only solvable ideal. It has central radical, or is reductive, if its radical equals its center.

**Definition (Killing Lie algebra).** A Lie algebra is Killing if its Killing form is non-degenerate, that is, if $L^\perp = 0$.

Over a field of characteristic $0$ the three conditions agree: Killing, semisimple, and trivial radical. In positive characteristic, Killing implies semisimple, and semisimple implies trivial radical, but the converse implications can fail.

### Theorems and proofs

**Proposition (The trace form is symmetric and invariant).** For $x, y, z \in L$, $B_M(x, y) = B_M(y, x)$ and $B_M([x, y], z) = B_M(x, [y, z])$.

*Proof.* Write $a = \varphi(x)$, $b = \varphi(y)$, $c = \varphi(z)$. Symmetry is $\operatorname{tr}(ab) = \operatorname{tr}(ba)$. For invariance, $\varphi$ is a morphism, so
$$\operatorname{tr}((ab - ba) c) - \operatorname{tr}(a (bc - cb)) = \operatorname{tr}(acb) - \operatorname{tr}(bac) = 0,$$
because the trace is invariant under cyclic permutations. $\square$

**Proposition (Orthogonals of ideals).** If $B$ is an invariant form on $L$ and $I$ is an ideal, then $I^\perp$ is an ideal.

*Proof.* Let $z \in I^\perp$, $x \in L$ and $i \in I$. Then $B([x, z], i) = -B([z, x], i) = -B(z, [x, i]) = 0$, because $[x, i] \in I$. $\square$

**Proposition (The Killing form of an ideal).** Let $I$ be an ideal of a finite-dimensional Lie algebra $L$ over $K$. Then the Killing form of $I$ is the restriction of the Killing form of $L$ to $I$.

*Proof.* For $x, y \in I$ the map $a = \operatorname{ad} x \circ \operatorname{ad} y$ sends $L$ into $I$. In a basis of $L$ that extends a basis of $I$, the matrix of $a$ has the block form $\begin{pmatrix} a|_I & * \\ 0 & 0 \end{pmatrix}$, so $\operatorname{tr}_L(a) = \operatorname{tr}_I(a|_I)$, which is the Killing form of $I$. $\square$

**Proposition (Nilpotent algebras and abelian ideals).**

1. If $L$ is nilpotent and $R$ is reduced, then $\kappa = 0$.
2. If $A$ is an abelian ideal of $L$, then $\kappa(A, L) = 0$, so $A \subseteq L^\perp$.

*Proof.* For the first claim, $\operatorname{ad} x \circ \operatorname{ad} y$ sends $C^k L$ into $C^{k+2} L$, so it is nilpotent, and over a reduced ring a nilpotent endomorphism of a free module has trace $0$. For the second, let $a \in A$, $x \in L$ and $u = \operatorname{ad} a \circ \operatorname{ad} x$. Then $u(L) \subseteq A$, and $u(A) = [a, [x, A]] \subseteq [a, A] = 0$. So $u^2 = 0$ and $\kappa(a, x) = \operatorname{tr}(u) = 0$. $\square$

**Theorem (Killing algebras are semisimple).** Let $L$ be a finite-dimensional Killing Lie algebra over $K$.

1. $L$ has no nonzero abelian ideal, and its radical is $0$.
2. For each ideal $I$, $L = I \oplus I^\perp$.
3. $L$ is the direct sum of simple ideals, so $L$ is semisimple.

*Proof.* By the proposition on abelian ideals, each abelian ideal lies in $L^\perp = 0$. If the radical $S$ is nonzero, then the last nonzero term of its derived series is an abelian ideal of $L$, a contradiction. For the second claim, let $J = I \cap I^\perp$, an ideal. For $j_1, j_2 \in J$ and $x \in L$, invariance gives $\kappa([j_1, j_2], x) = \kappa(j_1, [j_2, x]) = 0$, because $j_1 \in I^\perp$ and $[j_2, x] \in I$. So $[J, J] \subseteq L^\perp = 0$, $J$ is abelian, and $J = 0$. A non-degenerate form gives $\dim I^\perp = \dim L - \dim I$, so $L = I \oplus I^\perp$. For the third claim, use induction on $\dim L$. If $L$ has no ideal other than $0$ and $L$, then it is simple, since it is not abelian. Otherwise, take an ideal $0 \neq I \neq L$. Then $[I, I^\perp] \subseteq I \cap I^\perp = 0$, so each ideal of $I$ is an ideal of $L$, and the Killing forms of $I$ and $I^\perp$ are the restrictions of $\kappa$, which are non-degenerate because $L$ is their orthogonal sum. By induction, $I$ and $I^\perp$ are direct sums of simple ideals. $\square$

**Theorem (Cartan's criterion for solvability).** Let $K$ have characteristic $0$ and let $L$ be finite-dimensional over $K$. If $\kappa(x, y) = 0$ for all $x \in L$ and $y \in [L, L]$, then $L$ is solvable.

*Proof sketch.* The key step is a statement on a subalgebra $L \subseteq \mathfrak{gl}(V)$: if $\operatorname{tr}(x y) = 0$ for all $x \in [L, L]$ and $y \in L$, then each $x \in [L, L]$ is nilpotent. Write $x = s + n$, the Jordan-Chevalley decomposition with $s$ semisimple, $n$ nilpotent and $s n = n s$. After an extension of scalars to an algebraic closure, let $a_1, \dots, a_m$ be the eigenvalues of $s$, let $f$ be a $\mathbb{Q}$-linear form on their $\mathbb{Q}$-span, and let $y$ act by $f(a_i)$ on the eigenspace of $s$ for $a_i$. Then $\operatorname{ad} y$ is a polynomial without constant term in $\operatorname{ad} s$, so in $\operatorname{ad} x$, and the hypothesis with the invariance of the trace form gives $\operatorname{tr}(x y) = \sum_i f(a_i) a_i = 0$. Apply $f$: $\sum_i f(a_i)^2 = 0$, so $f(a_i) = 0$ for each $f$, all $a_i$ are $0$, and $s = 0$. Apply this to $\operatorname{ad}(L) \subseteq \mathfrak{gl}(L)$: each element of $\operatorname{ad}([L, L])$ is nilpotent, so $[L, L]$ is nilpotent by Engel's theorem, and $L$ is solvable as an extension of the abelian algebra $L / [L, L]$ by a solvable ideal. $\square$

**Theorem (Cartan's criterion for semisimplicity).** Let $K$ have characteristic $0$ and $L$ be finite-dimensional over $K$. Then $L$ is Killing if and only if its radical is $0$.

*Proof.* If $L$ is Killing, its radical is $0$ by the first theorem. Conversely, suppose the radical is $0$ and let $S = L^\perp$, an ideal. By the proposition on the Killing form of an ideal, the Killing form of $S$ is the restriction of $\kappa$, which is $0$ on $S$. So the hypothesis of Cartan's criterion for solvability holds for $S$, and $S$ is solvable. So $S$ lies in the radical, and $S = 0$. $\square$

**Theorem (Derivations of Killing algebras are inner).** If $L$ is a finite-dimensional Killing Lie algebra over $K$, then each derivation of $L$ is inner: $\operatorname{Der}(L) = \operatorname{ad}(L)$.

*Proof.* Write $D = \operatorname{Der}(L)$ and $A = \operatorname{ad}(L)$. The center of $L$ is an abelian ideal, so it is $0$, and $\operatorname{ad} : L \to A$ is an isomorphism; so the Killing form $\kappa_A$ of $A$ is non-degenerate. The algebra $A$ is an ideal of $D$, by the previous chapter, so $\kappa_A$ is the restriction of the Killing form $\kappa_D$ of $D$. Let $I = A^\perp$ in $D$ for $\kappa_D$, an ideal of $D$. Then $I \cap A = 0$ because $\kappa_A$ is non-degenerate, and $\dim I \geq \dim D - \dim A$. Since $I$ and $A$ are ideals, $[I, A] \subseteq I \cap A = 0$. For $\delta \in I$ and $x \in L$, $\operatorname{ad}(\delta x) = [\delta, \operatorname{ad} x] = 0$, so $\delta x$ is central, and $\delta x = 0$. So $I = 0$ and $D = A$. $\square$

### Examples

**Example (The Killing form of sl2).** In the basis $e, h, f$ of $\mathfrak{sl}_2(K)$, the previous chapter gives $\operatorname{ad} h = \operatorname{diag}(2, 0, -2)$, and $\operatorname{ad} e$, $\operatorname{ad} f$ with $e \mapsto 0, h \mapsto -2e, f \mapsto h$ and $e \mapsto -h, h \mapsto 2f, f \mapsto 0$. Then $\kappa(h, h) = 4 + 0 + 4 = 8$. The map $\operatorname{ad} e \circ \operatorname{ad} f$ sends $e \mapsto 2e$, $h \mapsto 2h$, $f \mapsto 0$, so $\kappa(e, f) = 4$. The maps $\operatorname{ad} e \circ \operatorname{ad} e$ and $\operatorname{ad} e \circ \operatorname{ad} h$ are nilpotent, so $\kappa(e, e) = \kappa(e, h) = 0$, and in the same way $\kappa(f, f) = \kappa(f, h) = 0$. The Gram matrix is
$$\begin{pmatrix} 0 & 0 & 4 \\ 0 & 8 & 0 \\ 4 & 0 & 0 \end{pmatrix},$$
with determinant $-128 = -2^7$. So $\kappa$ is non-degenerate when the characteristic is not $2$, and $\mathfrak{sl}_2(K)$ is a Killing algebra. A comparison with $\operatorname{tr}(hh) = 2$ and $\operatorname{tr}(ef) = 1$ gives $\kappa(x, y) = 4 \operatorname{tr}(x y)$.

**Example (A solvable algebra).** Let $L$ have basis $x, y$ with $[x, y] = y$. Then $\operatorname{ad} x = \operatorname{diag}(0, 1)$, and $\operatorname{ad} y$ sends $x \mapsto -y$, $y \mapsto 0$. So $\kappa(x, x) = 1$, $\kappa(x, y) = 0$ and $\kappa(y, y) = 0$. The form vanishes on $L \times [L, L] = L \times K y$, as Cartan's criterion requires, and its kernel is $K y$. The form is not $0$, so the converse of the first claim of the proposition on nilpotent algebras fails: a solvable algebra can have a nonzero Killing form.

**Example (gl_n is reductive).** In $\mathfrak{gl}_n(K)$ the identity $I$ is central, so $\operatorname{ad} I = 0$ and $\kappa(I, y) = 0$ for each $y$. The Killing form is degenerate, and $\mathfrak{gl}_n$ is not semisimple. In characteristic $0$, $\mathfrak{gl}_n = \mathfrak{sl}_n \oplus K I$, where $\mathfrak{sl}_n$ is semisimple and $K I$ is the center, which is also the radical. So $\mathfrak{gl}_n$ has central radical.

**Counterexample (Characteristic 2).** If $K$ has characteristic $2$, then in $\mathfrak{sl}_2(K)$ the brackets are $[h, e] = 2e = 0$, $[h, f] = 0$ and $[e, f] = h$. This is the Heisenberg algebra, which is nilpotent, so its Killing form is $0$ and the Gram matrix above reduces to $0$ mod $2$.

### The library around it

::: mathlib
`LieModule.traceForm` · `Mathlib.Algebra.Lie.TraceForm`

`LieModule.traceForm R L M : LinearMap.BilinForm R L` has `traceForm_apply_apply`, the formula of the definition. `traceForm_isSymm` and `traceForm_apply_lie_apply : B ⁅x, y⁆ z = B x ⁅y, z⁆` are the proposition on symmetry and invariance, and `traceForm_lieInvariant` states the invariance in the form of `LinearMap.BilinForm.lieInvariant`. `traceForm_eq_zero_of_isNilpotent` needs `[IsReduced R]`. `killingForm R L` is an abbreviation for `traceForm R L L`, with `killingForm_apply_apply`. For an ideal, `LieIdeal.killingCompl R L I` is the orthogonal, with `mem_killingCompl`, `LieIdeal.killingForm_eq` is the restriction theorem over a principal ideal domain, and `LieIdeal.le_killingCompl_top_of_isLieAbelian` is the claim on abelian ideals.

<?decl LieModule.traceForm?>
:::

::: mathlib
`LieAlgebra.IsSemisimple` · `Mathlib.Algebra.Lie.Semisimple.Defs`

`LieAlgebra.IsSimple R L` has the fields `eq_bot_or_eq_top` and `non_abelian`. `LieAlgebra.IsSemisimple R L` has three fields: `sSup_atoms_eq_top`, `sSupIndep_isAtom` and `non_abelian_of_isAtom`, so the atoms, the minimal nonzero ideals, are independent, non-abelian and span `L`. `LieAlgebra.HasTrivialRadical R L` states `radical R L = ⊥`, and `HasCentralRadical` states that the radical equals the center. In `Mathlib.Algebra.Lie.Semisimple.Basic`, `IsSemisimple.isSimple_of_isAtom` shows that the atoms are simple, `IsSimple.instIsSemisimple` and `IsSemisimple.instHasTrivialRadical` are the implications, `hasTrivialRadical_iff_no_abelian_ideals` and `hasTrivialRadical_iff_no_solvable_ideals` describe the radical, and `ad_ker_eq_bot_of_hasTrivialRadical` gives a faithful adjoint map. In `Semisimple.Lemmas`, `trace_toEnd_eq_zero` extends a vanishing trace from a set to its Lie span, and `hasTrivialRadical_of_isIrreducible_of_isFaithful` gives a trivial radical for a faithful irreducible module.

<?decl LieAlgebra.IsSemisimple?>
:::

::: mathlib
`LieAlgebra.IsKilling` · `Mathlib.Algebra.Lie.Killing`

`LieAlgebra.IsKilling R L` has the single field `killingCompl_top_eq_bot`, and `IsKilling.killingForm_nondegenerate` gives the non-degeneracy. The name records the non-degenerate Killing form; it is not a standard term of the literature. Over a field, `IsKilling.instSemisimple` is the theorem on Killing algebras, `LieIdeal.isCompl_killingCompl` is the decomposition `L = I ⊕ I^⊥`, and `IsKilling.ideal_eq_bot_of_isLieAbelian` kills the abelian ideals. Over a principal ideal domain, `IsKilling.instHasTrivialRadical` gives the trivial radical. In `Mathlib.Algebra.Lie.InvariantForm`, `LieAlgebra.InvariantForm.orthogonal`, `orthogonal_isCompl` and `isSemisimple_of_nondegenerate` prove the same results for any non-degenerate reflexive invariant form, under the hypothesis that no atom is abelian.

<?decl LieAlgebra.IsKilling?>
:::

::: mathlib
`LieAlgebra.isSolvable_of_killingForm_apply_lie_eq_zero` · `Mathlib.Algebra.Lie.CartanCriterion`

Cartan's criterion for solvability holds over a domain `R` with `[CharZero R]`, for `L` Noetherian and free over `R`, with the hypothesis `∀ x y, y ∈ derivedSeries R L 1 → killingForm R L x y = 0`. `LieIdeal.isSolvable_of_killingForm_apply_lie_eq_zero` is the version for an ideal. The key step is `LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero`. `killingCompl_top_le_radical` states `L^⊥ ≤ radical`, and `HasTrivialRadical.instIsKilling` is the criterion for semisimplicity, with `hasTrivialRadical_iff_isKilling` over a principal ideal domain. The source lists the converse of the solvability criterion as future work, so the index of this edition has no declaration for it.

<?decl LieAlgebra.isSolvable_of_killingForm_apply_lie_eq_zero?>
:::

::: mathlib
`LieDerivation.IsKilling.exists_eq_ad` · `Mathlib.Algebra.Lie.Derivation.Killing`

Over a field, for `[Module.Finite R L]` and `[IsKilling R L]`, `exists_eq_ad D : ∃ x, ad R L x = D` states that each derivation is inner, and `range_ad_eq_top` is the form `(ad R L).range = ⊤`. The proof of the library follows the text, with `ad_mem_orthogonal_of_mem_orthogonal` for the step $[\delta, \operatorname{ad} x] = \operatorname{ad}(\delta x)$ in the orthogonal.

<?decl LieDerivation.IsKilling.exists_eq_ad?>
:::

::: mathlib
`LieAlgebra.ad_mem_adjoin_of_isSemisimple` · `Mathlib.Algebra.Lie.AdjointAction.JordanChevalley`

For a perfect field `K` and commuting `n`, `s` in `Module.End K V` with `n` nilpotent and `s` semisimple, `ad_mem_adjoin_of_isSemisimple` states that `ad s` lies in `K[ad (n + s)]`, the algebra generated by `ad (n + s)`, and `ad_mem_adjoin_of_isNilpotent` is the same for `ad n`. These are the polynomial statements in the proof of Cartan's criterion. The decomposition itself is `Module.End.exists_isNilpotent_isSemisimple` in `Mathlib.LinearAlgebra.JordanChevalley`.

<?decl LieAlgebra.ad_mem_adjoin_of_isSemisimple?>
:::

Common errors of a learner: The first error is to use `LieAlgebra.IsSemisimple` for the classical definition with a zero radical; that is `HasTrivialRadical`, and the two agree only in characteristic $0$ for finite-dimensional algebras. The second error is to search for a lemma about `LieAlgebra.killingForm`; the Killing form is the top-level `killingForm R L`. The third error is to expect the converse of Cartan's solvability criterion in the library. The fourth error is to forget the hypotheses `[Module.Free R L]` and `[IsNoetherian R L]`, which the trace needs.

### Exercises

1. (A) Show that the Killing form is invariant under each automorphism: $\kappa(\sigma x, \sigma y) = \kappa(x, y)$. Hint: $\operatorname{ad}(\sigma x) = \sigma \circ \operatorname{ad} x \circ \sigma^{-1}$.
2. (A) Compute the Killing form of the Heisenberg algebra $[x, y] = z$ over $\mathbb{Q}$, and check the proposition on nilpotent algebras. Hint: $\operatorname{ad} u \circ \operatorname{ad} v$ sends everything into $K z$ and kills $z$.
3. (A) Show that a direct sum of two Killing algebras is a Killing algebra. Hint: the Killing form of $L_1 \times L_2$ is the orthogonal sum of the two Killing forms.
4. (B) Compute the Killing form of $\mathfrak{so}_3(\mathbb{R})$ in the basis of the cross product, $[e_1, e_2] = e_3$ and its cyclic forms, and show that it is negative definite. Hint: $\operatorname{ad} e_1$ has the matrix with $e_2 \mapsto e_3$, $e_3 \mapsto -e_2$; the answer is $-2$ times the identity.
5. (B) Show that each ideal of a Killing algebra over $K$ is a Killing algebra, and that $[L, L] = L$. Hint: use the decomposition $L = I \oplus I^\perp$ and the fact that a simple algebra satisfies $[L, L] = L$.
6. (C) Show that the Killing form of $\mathfrak{gl}_n(K)$ is $\kappa(x, y) = 2n \operatorname{tr}(x y) - 2 \operatorname{tr}(x) \operatorname{tr}(y)$. Hint: compute $\operatorname{tr}(\operatorname{ad} E_{ij} \circ \operatorname{ad} E_{kl})$ on the basis $E_{pq}$, or use $\operatorname{ad} x = \lambda_x - \rho_x$ and $\operatorname{tr}(\lambda_a \rho_b) = \operatorname{tr}(a) \operatorname{tr}(b)$.

### Notes and history

Killing introduced the form that carries his name in his work on the classification of the simple Lie algebras over the complex numbers in the late 1880s, and Cartan, in his thesis of 1894, proved the two criteria and completed the classification. Weyl later proved the complete reducibility of the representations of a semisimple algebra. Serre's book of 1966 gave the presentation of a semisimple algebra by generators and relations, which the root systems of the next chapters lead to.

The Mathlib files are by these authors, read from their headers: `TraceForm`, `Killing`, `Semisimple.Basic` and `Semisimple.Lemmas` (all under `Mathlib.Algebra.Lie`) by Oliver Nash; `Semisimple.Defs` by Oliver Nash and Johan Commelin; `InvariantForm` by Johan Commelin; `CartanCriterion` and `AdjointAction.JordanChevalley` by Janos Wolosz; and `Derivation.Killing` by Frédéric Marbach.

### Reference

<?reference?>
