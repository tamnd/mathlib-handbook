---
title: Algebraic closure
kind: theory
modules:
  - Mathlib.FieldTheory.IsAlgClosed.Basic
  - Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
  - Mathlib.FieldTheory.AlgebraicClosure
  - Mathlib.FieldTheory.IsAlgClosed.Classification
  - Mathlib.FieldTheory.Extension
  - Mathlib.FieldTheory.IsRealClosed.Basic
  - Mathlib.FieldTheory.IsRealClosed.Real
  - Mathlib.FieldTheory.IsAlgClosed.Spectrum
explains:
  E3: [IsAlgClosed, IsAlgClosure, AlgebraicClosure, IsAlgClosed.lift, IsAlgClosure.equiv, algebraicClosure]
  E2: [IsAlgClosed.exists_root, IsAlgClosed.of_exists_root, IsAlgClosed.splits, IsAlgClosed.degree_eq_one_of_irreducible, IsAlgClosed.algebraMap_bijective_of_isIntegral, IsAlgClosure.of_splits, AlgebraicClosure.maxIdeal, AlgebraicClosure.spanCoeffs, AlgebraicClosure.spanCoeffs_ne_top, AlgebraicClosure.subProdXSubC, AlgebraicClosure.Vars, AlgebraicClosure.Monics, AlgebraicClosure.toSplittingField, mem_algebraicClosure_iff, IsAlgClosed.algebraicClosure_eq_bot_iff, IntermediateField.exists_algHom_of_splits, IsAlgClosed.ringEquiv_of_equiv_of_char_eq, IsAlgClosed.equivOfTranscendenceBasis, IsRealClosed]
  E1: auto
families: []
requires: [V11.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Algebraic closure

### Overview

Section 1 built a field for one polynomial. This section builds one field for all polynomials over $K$ at once: an algebraic closure $\overline K$, an algebraic extension in which each polynomial has a root.

The section proves that each field has an algebraic closure, with the construction of Artin by a polynomial ring in many variables and a maximal ideal. It proves that embeddings into an algebraically closed field extend along algebraic extensions, and deduces that the algebraic closure is unique up to isomorphism.

It uses maximal ideals and the lemma of Zorn from Volume 6, Chapter 2.

### Definitions

**Definition (Algebraically closed field).** A field $M$ is algebraically closed if each polynomial $f \in M[X]$ of positive degree has a root in $M$.

**Definition (Algebraic closure).** An algebraic closure of $K$ is an algebraic extension $L/K$ such that $L$ is algebraically closed.

::: mathlib
`IsAlgClosed` · `Mathlib.FieldTheory.IsAlgClosed.Basic`

`IsAlgClosed k` is a class with one field, `splits : ∀ p : k[X], p.Splits`. The form of the definition above is a theorem: `IsAlgClosed.exists_root p : p.degree ≠ 0 → ∃ x, p.IsRoot x`. To prove that a field is algebraically closed, `IsAlgClosed.of_exists_root` asks only for roots of monic irreducible polynomials.

<?decl IsAlgClosed?>
:::

::: mathlib
`IsAlgClosure` · `Mathlib.FieldTheory.IsAlgClosed.Basic`

`IsAlgClosure R K` is a class with two fields: `IsAlgClosed K` and `Algebra.IsAlgebraic R K`. It allows a ring `R`, not only a field. `IsAlgClosure.of_splits` gives it for an integral extension over which each monic irreducible polynomial splits: this is the lemma below.

<?decl IsAlgClosure?>
:::

### Theorems and proofs

**Theorem (Forms of algebraic closedness).** For a field $M$ the following are equivalent.
1. $M$ is algebraically closed.
2. Each polynomial over $M$ splits over $M$.
3. Each irreducible polynomial over $M$ has degree $1$.
4. Each algebraic extension $L/M$ is trivial: $L = M$.

*Proof.* (1 implies 2.) Induction on the degree: a root $a$ of $f$ gives $f = (X - a)g$ with $\deg g = \deg f - 1$. (2 implies 3.) An irreducible $f$ is a product of linear factors, so it is one of them, up to a unit. (3 implies 4.) For $\alpha \in L$ algebraic over $M$, $m_\alpha$ is irreducible, so $m_\alpha = X - a$ and $\alpha = a \in M$. (4 implies 1.) A polynomial $f$ of positive degree has a root $\alpha$ in an extension of finite degree, by Kronecker (Section 1). That extension $M(\alpha)$ is algebraic, so $M(\alpha) = M$ and $\alpha \in M$. $\square$

In Mathlib, (3) is `IsAlgClosed.degree_eq_one_of_irreducible`, and a form of (4) is `IsAlgClosed.algebraMap_bijective_of_isIntegral`.

**Lemma (Splitting over the base suffices).** Let $L/K$ be algebraic, and suppose each polynomial in $K[X]$ splits over $L$. Then $L$ is algebraically closed.

*Proof.* Let $g \in L[X]$ have positive degree. By Kronecker, $g$ has a root $\beta$ in some extension $E$ of $L$. Then $\beta$ is algebraic over $L$, and $L$ is algebraic over $K$, so $\beta$ is algebraic over $K$ by transitivity (Chapter 2, Section 1). Its minimal polynomial $m = m_{\beta,K}$ splits over $L$: $m = \prod_i (X - l_i)$ with $l_i \in L$. In $E$, $0 = m(\beta) = \prod_i (\beta - l_i)$, so $\beta = l_i$ for some $i$. So $\beta \in L$ is a root of $g$ in $L$. $\square$

**Theorem (Existence of an algebraic closure).** Each field $K$ has an algebraic closure.

*Proof.* Let $\mathcal{M}$ be the set of monic polynomials in $K[X]$ of positive degree. For each $f \in \mathcal{M}$ of degree $n_f$, take $n_f$ variables $X_{f,1}, \dots, X_{f,n_f}$, and let $R = K[X_{f,i}]$ be the polynomial ring in all of them. In $R[T]$ write
$$f(T) - \prod_{i=1}^{n_f} (T - X_{f,i}) = \sum_{j < n_f} c_{f,j}\,T^j, \qquad c_{f,j} \in R.$$
Let $I$ be the ideal of $R$ generated by all $c_{f,j}$.

First, $I \neq R$. Suppose $1 \in I$. Then $1 = \sum_k r_k c_{f_k, j_k}$, a finite sum, in which only finitely many $f_1, \dots, f_m$ occur. Let $E$ be a splitting field of $f_1 \cdots f_m$ over $K$ (Section 1). In $E[T]$ each $f_k$ is a product $\prod_i (T - \beta_{k,i})$. Let $\psi \colon R \to E$ be the $K$-algebra map with $X_{f_k,i} \mapsto \beta_{k,i}$ and every other variable sent to $0$. Then $\psi$ maps $f_k(T) - \prod_i (T - X_{f_k,i})$ to $0$, so $\psi(c_{f_k,j}) = 0$ for each $k$ and $j$. Applying $\psi$ to the sum gives $1 = 0$ in $E$, a contradiction.

By Volume 6, Chapter 2, the proper ideal $I$ lies in a maximal ideal $\mathfrak m$. Let $L = R/\mathfrak m$, a field and an extension of $K$, and let $x_{f,i}$ be the class of $X_{f,i}$. Since $c_{f,j} \in \mathfrak m$, the image of the identity above in $L[T]$ is $f(T) = \prod_i (T - x_{f,i})$. So each $f \in \mathcal{M}$ splits over $L$, and each $x_{f,i}$ is a root of $f$, so it is algebraic over $K$.

The algebraic elements of $L$ form a subfield (Chapter 2, Section 1). It contains all $x_{f,i}$, which generate $L$ as a ring over $K$. So $L/K$ is algebraic. Each nonzero polynomial over $K$ is a constant times an element of $\mathcal{M}$ or a constant, so it splits over $L$. By the lemma, $L$ is algebraically closed. $\square$

::: mathlib
`AlgebraicClosure` · `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`

`AlgebraicClosure k` follows the proof. `AlgebraicClosure.Monics k` is the type of monic polynomials of positive degree, `AlgebraicClosure.Vars k` indexes the variables $X_{f,i}$, and `AlgebraicClosure.subProdXSubC f` is the polynomial $f - \prod (T - X_{f,i})$ over `MvPolynomial (Vars k) k`. `AlgebraicClosure.spanCoeffs k` is the ideal $I$. The step $I \neq R$ is `AlgebraicClosure.spanCoeffs_ne_top`, with the map $\psi$ as `AlgebraicClosure.toSplittingField s`, into the splitting field of a finite product. `AlgebraicClosure.maxIdeal k` is a maximal ideal that contains `spanCoeffs k`, and `AlgebraicClosure k` is the quotient. The instances `AlgebraicClosure.isAlgClosed` and `AlgebraicClosure.isAlgebraic` complete the proof.

<?decl AlgebraicClosure?>
:::

**Theorem (Extension of embeddings).** Let $L/K$ be algebraic, $M$ algebraically closed and $\varphi \colon K \to M$ a ring map. Then $\varphi$ extends to a ring map $\sigma \colon L \to M$.

*Proof.* Let $\mathcal{P}$ be the set of pairs $(E, \tau)$, where $E$ is an intermediate field of $L/K$ and $\tau \colon E \to M$ extends $\varphi$. Order it by $(E, \tau) \leq (E', \tau')$ if $E \subseteq E'$ and $\tau'$ extends $\tau$. A chain $(E_s, \tau_s)$ has the upper bound $(\bigcup E_s, \tau)$, with $\tau(x) = \tau_s(x)$ for $x \in E_s$: the union of a chain of fields is a field, and $\tau$ is well defined since the $\tau_s$ agree. By the lemma of Zorn there is a maximal $(E, \tau)$.

Suppose $E \neq L$ and take $\alpha \in L \setminus E$. It is algebraic over $K$, so over $E$. Let $g = m_{\alpha,E}$. The polynomial $\tau(g) \in M[X]$ has positive degree, so it has a root $\beta \in M$. As in Section 1, $p \mapsto \tau(p)(\beta)$ induces $\tau' \colon E(\alpha) \to M$ that extends $\tau$. This contradicts maximality. So $E = L$. $\square$

::: mathlib
`IsAlgClosed.lift` · `Mathlib.FieldTheory.IsAlgClosed.Basic`

`IsAlgClosed.lift : S →ₐ[R] M` for `[IsAlgClosed M]` and `[Algebra.IsAlgebraic R S]`. It is chosen by the axiom of choice. The Zorn argument for intermediate fields is in `Mathlib.FieldTheory.Extension`, with the type `IntermediateField.Lifts` of pairs. Its main result `IntermediateField.exists_algHom_of_splits` needs only that each minimal polynomial splits over the target, not that the target is algebraically closed.

<?decl IsAlgClosed.lift?>
:::

**Corollary (Uniqueness of the algebraic closure).** Let $L$ and $L'$ be algebraic closures of $K$. Then there is an isomorphism $L \to L'$ of $K$-algebras.

*Proof.* The theorem gives a $K$-algebra map $\sigma \colon L \to L'$, injective since $L$ is a field. Its image $\sigma(L) \cong L$ is algebraically closed. The extension $L'/\sigma(L)$ is algebraic, since each element of $L'$ is algebraic over $K \subseteq \sigma(L)$. By the forms of algebraic closedness, $L' = \sigma(L)$. $\square$

The isomorphism is not unique. Complex conjugation restricts to a nontrivial automorphism of the algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$ in $\mathbb{C}$.

::: mathlib
`IsAlgClosure.equiv` · `Mathlib.FieldTheory.IsAlgClosed.Basic`

`IsAlgClosure.equiv R L M : L ≃ₐ[R] M` for two algebraic closures. As for `lift`, the choice is arbitrary.

<?decl IsAlgClosure.equiv?>
:::

**Theorem (Algebraic closure inside a closed field).** Let $E/K$ be an extension with $E$ algebraically closed. Then the field $A$ of elements of $E$ algebraic over $K$ is an algebraic closure of $K$.

*Proof.* $A$ is a field, algebraic over $K$. Let $g \in A[X]$ have positive degree. It has a root $\beta \in E$. Then $\beta$ is algebraic over $A$, so over $K$ by transitivity. So $\beta \in A$. $\square$

::: mathlib
`algebraicClosure` · `Mathlib.FieldTheory.AlgebraicClosure`

`algebraicClosure F E : IntermediateField F E` is the field $A$, with `mem_algebraicClosure_iff : x ∈ algebraicClosure F E ↔ IsAlgebraic F x`. The instance `algebraicClosure.isAlgClosure` is the theorem. The lemma `IsAlgClosed.algebraicClosure_eq_bot_iff` says that `algebraicClosure F E = ⊥` exactly when `F` is algebraically closed.

<?decl algebraicClosure?>
:::

**Theorem (Classification).** Two algebraically closed fields are isomorphic if and only if they have the same characteristic and transcendence bases of the same cardinality over their prime fields. Two uncountable algebraically closed fields of the same characteristic and the same cardinality are isomorphic.

For the first statement, a bijection of transcendence bases gives an isomorphism of the fields $P(S)$ of rational functions, and each field is an algebraic closure of $P(S)$, so the uniqueness corollary applies. In Mathlib the two statements are `IsAlgClosed.equivOfTranscendenceBasis` and `IsAlgClosed.ringEquiv_of_equiv_of_char_eq`.

### Examples

**Example (An algebraically closed field is infinite).** Let $M$ be a finite field with the elements $a_1, \dots, a_n$. The polynomial $f = (X - a_1)\cdots(X - a_n) + 1$ has degree $n \geq 1$, and $f(a_i) = 1$ for each $i$. So $f$ has no root, and $M$ is not algebraically closed. So the algebraic closure $\overline{\mathbb{F}}_p$ is infinite. Chapter 7 shows that it is the union of the finite fields $\mathbb{F}_{p^n}$. In Mathlib this is the instance `IsAlgClosed.instInfinite`.

**Example (The algebraic numbers).** By the theorem above, $\overline{\mathbb{Q}} = $ `algebraicClosure ℚ ℂ` is an algebraic closure of $\mathbb{Q}$, since $\mathbb{C}$ is algebraically closed. The proof of the last fact uses analysis, and in Mathlib it is the instance `Complex.isAlgClosed`. The field $\overline{\mathbb{Q}}$ is countable (Chapter 2, Section 1, Exercise 8). So $\mathbb{C}$ is algebraically closed but not an algebraic closure of $\mathbb{Q}$: the algebraic condition in the definition is needed for uniqueness.

**Example (Algebraic is needed for extension).** The extension theorem fails without the hypothesis that $L/K$ is algebraic. Take $K = M = \mathbb{C}$, $\varphi$ the identity and $L = \mathbb{C}(t)$. A $\mathbb{C}$-algebra map $\sigma \colon \mathbb{C}(t) \to \mathbb{C}$ sends $t$ to some $c \in \mathbb{C}$. Then $\sigma(t - c) = 0$, but $t - c$ is a unit of $\mathbb{C}(t)$, and a ring map sends units to units. So no $\sigma$ exists.

**Example (The real numbers).** $\mathbb{R}$ is not algebraically closed, since $X^2 + 1$ has no root. It is real closed: each polynomial of odd degree has a root, by the intermediate value theorem, and each positive element is a square. Then $\mathbb{R}(i) = \mathbb{C}$ is algebraically closed. In Mathlib, `IsRealClosed` is the class, and `instIsRealClosedReal` is the instance for `ℝ`.

### The library around it

The module `Mathlib.FieldTheory.IsAlgClosed.Spectrum` uses algebraic closure for linear algebra. Let $A$ be an algebra over a field $k$ and $a \in A$. The spectrum $\sigma(a)$ is the set of $\lambda \in k$ such that $a - \lambda$ is not invertible. For a polynomial $p$, `spectrum.subset_polynomial_aeval` gives $p(\sigma(a)) \subseteq \sigma(p(a))$ over any field. Over an algebraically closed field, the spectral mapping theorem gives equality, $\sigma(p(a)) = p(\sigma(a))$, when $\deg p > 0$ (`spectrum.map_polynomial_aeval_of_degree_pos`) or when $\sigma(a)$ is nonempty (`spectrum.map_polynomial_aeval_of_nonempty`). *Proof sketch.* Let $\mu \in k$. Since $k$ is algebraically closed, $p - \mu = c \prod_i (X - \lambda_i)$ with $c \neq 0$, so $p(a) - \mu = c \prod_i (a - \lambda_i)$. The factors commute, so the product is invertible if and only if each factor is. Thus $\mu \in \sigma(p(a))$ if and only if some root $\lambda_i$ of $p - \mu$ lies in $\sigma(a)$, that is, $\mu \in p(\sigma(a))$. $\square$ The case of powers is `spectrum.map_pow_of_pos`. The module also proves `spectrum.nonempty_of_isAlgClosed_of_finiteDimensional`: in a nontrivial algebra of finite dimension over an algebraically closed field, each element has an eigenvalue. For an idempotent $e$, `IsIdempotentElem.spectrum_subset` gives $\sigma(e) \subseteq \{0, 1\}$.

**Common errors of a learner.** The first error is to expect `IsAlgClosed.lift` to agree with a given embedding. It is arbitrary. The second error is to confuse `AlgebraicClosure K` with `algebraicClosure K E`. The third error is to use `IsAlgClosure ℚ ℂ`: it is false.

### Exercises

1. (A) Show that an algebraically closed field has no proper finite extension. Hint: the forms of algebraic closedness.

2. (A) Show that $\mathbb{F}_p$ is not algebraically closed by a polynomial of degree $p$. Hint: $X^p - X + 1$.

3. (A) Let $L$ be an algebraic closure of $K$ and $E$ an intermediate field. Show that $L$ is an algebraic closure of $E$. Hint: transitivity is not needed.

4. (B) Show that each finite extension of $K$ embeds into $\overline K$ over $K$. Hint: the extension theorem.

5. (B) Show that $\overline{\mathbb{Q}}$ has infinite degree over $\mathbb{Q}$ and that $[\mathbb{C}:\overline{\mathbb{Q}}]$ is infinite. Hint: the example in Chapter 2, Section 1, and countability.

6. (C) Let $K$ be infinite. Show that an algebraic closure of $K$ has the same cardinality as $K$. Hint: count the monic polynomials and their roots.

### Notes and history

Steinitz proved the existence and uniqueness of algebraic closures in 1910, with transfinite induction, and he proved the classification by characteristic and transcendence degree. The proof with one polynomial ring and a maximal ideal is due to Artin. Mathlib builds the algebraic closure in that way.

### Reference

<?reference?>
