---
title: Conjugates, norm and trace
kind: theory
modules:
  - Mathlib.FieldTheory.Minpoly.IsConjRoot
  - Mathlib.FieldTheory.Minpoly.ConjRootClass
  - Mathlib.RingTheory.Norm.Defs
  - Mathlib.RingTheory.Norm.Basic
  - Mathlib.RingTheory.Norm.Transitivity
  - Mathlib.RingTheory.Trace.Defs
  - Mathlib.RingTheory.Trace.Basic
  - Mathlib.RingTheory.Trace.Quotient
  - Mathlib.RingTheory.NormTrace
  - Mathlib.FieldTheory.NormalizedTrace
explains:
  E3: [IsConjRoot, Algebra.norm, Algebra.trace, Algebra.norm_eq_prod_roots, trace_eq_sum_roots, isConjRoot_iff_mem_minpoly_rootSet]
  E2: [Algebra.norm_eq_matrix_det, Algebra.trace_eq_matrix_trace, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, PowerBasis.trace_gen_eq_nextCoeff_minpoly, trace_eq_finrank_mul_minpoly_nextCoeff, Algebra.norm_norm, Algebra.trace_trace, Algebra.norm_algebraMap, Algebra.trace_algebraMap, Algebra.norm_eq_zero_iff, Algebra.traceForm, traceForm_nondegenerate, trace_eq_sum_embeddings, Algebra.norm_eq_prod_embeddings, Algebra.norm_eq_one_of_not_exists_basis, Algebra.trace_eq_zero_of_not_exists_basis, ConjRootClass, isConjRoot_of_algEquiv, Algebra.normalizedTrace]
  E1: auto
families: []
requires: [V11.C01, V07.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Conjugates, norm and trace

### Overview

The numbers $\sqrt 2$ and $-\sqrt 2$ cannot be told apart by an equation over $\mathbb{Q}$: they have the same minimal polynomial. Such elements are conjugate. This section proves that the embeddings of $K(\alpha)$ into a field $E$ correspond to the roots of $m_\alpha$ in $E$. So the conjugates of $\alpha$ are the possible images of $\alpha$. This count of embeddings is the start of Galois theory.

The section then defines two maps $L \to K$ for a finite extension: the norm and the trace. They are the determinant and the trace of the multiplication map $x \mapsto \alpha x$ on the $K$-vector space $L$. The section computes them from the coefficients of $m_\alpha$ and expresses them as the product and the sum of the conjugates.

The section needs Section 2, Chapter 1, and the determinant, the trace, the characteristic polynomial and the theorem of Cayley-Hamilton from Volume 7, Chapter 5.

### Definitions

**Definition (Conjugates).** Let $L/K$ be an extension and $\alpha, \beta \in L$ algebraic over $K$. Then $\beta$ is conjugate to $\alpha$ over $K$ if $m_{\alpha,K} = m_{\beta,K}$. Equivalently, $m_{\alpha,K}(\beta) = 0$: then $m_\alpha$ is monic, irreducible and has the root $\beta$, so it is $m_\beta$ by Section 2.

::: mathlib
`IsConjRoot` · `Mathlib.FieldTheory.Minpoly.IsConjRoot`

`IsConjRoot R x y` is defined as `minpoly R x = minpoly R y`. It is an equivalence relation, and the type of classes is `ConjRootClass K L`. For a non integral `x` the junk value `minpoly R x = 0` makes all non integral elements conjugate to each other, so the useful lemmas take `IsIntegral`. The second form of the definition is `isConjRoot_iff_mem_minpoly_rootSet`, and an automorphism `s` gives `isConjRoot_of_algEquiv x s : IsConjRoot R x (s x)`.

<?decl isConjRoot_iff_mem_minpoly_rootSet?>

<?decl IsConjRoot?>
:::

**Definition (Norm and trace).** Let $L/K$ be finite and $\alpha \in L$. Let $\mu_\alpha \colon L \to L$, $x \mapsto \alpha x$, the multiplication by $\alpha$, a $K$-linear map. The norm and the trace of $\alpha$ are
$$N_{L/K}(\alpha) = \det \mu_\alpha, \qquad \operatorname{Tr}_{L/K}(\alpha) = \operatorname{tr} \mu_\alpha.$$

Since $\mu_{\alpha\beta} = \mu_\alpha \circ \mu_\beta$ and $\mu_{\alpha + \beta} = \mu_\alpha + \mu_\beta$, the norm is multiplicative and the trace is $K$-linear. For $a \in K$, $\mu_a$ is $a$ times the identity, so $N(a) = a^n$ and $\operatorname{Tr}(a) = na$ with $n = [L:K]$. If $\alpha \neq 0$, then $\mu_\alpha$ is invertible with the inverse $\mu_{\alpha^{-1}}$, so $N(\alpha) \neq 0$.

::: mathlib
`Algebra.norm` · `Mathlib.RingTheory.Norm.Defs`

`Algebra.norm R : S →* R` is a monoid homomorphism, for any `R`-algebra `S`. It is the determinant of `Algebra.lmul R S s` when `S` has a finite basis over `R`, and the junk value `1` otherwise (`Algebra.norm_eq_one_of_not_exists_basis`). For a basis `b`, `Algebra.norm_eq_matrix_det` computes it as the determinant of `Algebra.leftMulMatrix b s`. The rules of the text are `Algebra.norm_algebraMap : norm R (algebraMap R S x) = x ^ finrank R S` and `Algebra.norm_eq_zero_iff`.

<?decl Algebra.norm?>
:::

::: mathlib
`Algebra.trace` · `Mathlib.RingTheory.Trace.Defs`

`Algebra.trace R S : S →ₗ[R] R` is an `R`-linear map, with the junk value `0` when there is no finite basis (`Algebra.trace_eq_zero_of_not_exists_basis`). `Algebra.trace_eq_matrix_trace` computes it with a basis, and `Algebra.trace_algebraMap` gives `trace R S (algebraMap R S x) = finrank R S • x`. Note the two explicit arguments: `Algebra.trace K L x`, but `Algebra.norm K x`.

<?decl Algebra.trace?>
:::

### Theorems and proofs

**Theorem (Embeddings of a simple extension).** Let $\alpha$ be algebraic over $K$ with minimal polynomial $m$, and let $E/K$ be an extension. The map $\sigma \mapsto \sigma(\alpha)$ is a bijection from the set of $K$-algebra homomorphisms $K(\alpha) \to E$ to the set of roots of $m$ in $E$. In particular there are at most $\deg m$ such homomorphisms.

*Proof.* Let $\sigma \colon K(\alpha) \to E$ fix $K$. Then $m(\sigma(\alpha)) = \sigma(m(\alpha)) = 0$, since $\sigma$ fixes the coefficients. So $\sigma(\alpha)$ is a root. The map is injective: each element of $K(\alpha) = K[\alpha]$ is $f(\alpha)$ with $f \in K[X]$, and $\sigma(f(\alpha)) = f(\sigma(\alpha))$ is determined by $\sigma(\alpha)$.

The map is surjective. Let $\beta \in E$ with $m(\beta) = 0$. Evaluation at $\beta$ is a $K$-algebra map $K[X] \to E$, and its kernel contains $m$. So it induces $K[X]/(m) \to E$, with $X \mapsto \beta$. Compose with the isomorphism $K(\alpha) \cong K[X]/(m)$ of Section 2, which sends $\alpha$ to the class of $X$. The result $\sigma$ satisfies $\sigma(\alpha) = \beta$. A polynomial of degree $n$ has at most $n$ roots in a field. $\square$

So $\alpha$ has exactly $\deg m$ images in $E$ when $m$ has $\deg m$ distinct roots in $E$. Chapter 4 calls such an $m$ separable.

::: mathlib
`IntermediateField.algHomAdjoinIntegralEquiv` · `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`

`algHomAdjoinIntegralEquiv F hα : (F⟮α⟯ →ₐ[F] K) ≃ {x // x ∈ (minpoly F α).aroots K}` is the bijection of the theorem. `aroots` is the multiset of roots in `K`. The count `IntermediateField.card_algHom_adjoin_integral` gives `deg m` homomorphisms when `m` is separable and splits in `K`.

<?decl IntermediateField.algHomAdjoinIntegralEquiv?>
:::

**Theorem (Norm and trace from the minimal polynomial).** Let $L/K$ be finite, $\alpha \in L$, and $m_\alpha = X^n + c_{n-1}X^{n-1} + \dots + c_0$. Let $d = [L:K(\alpha)]$. Then the characteristic polynomial of $\mu_\alpha$ on $L$ is $m_\alpha^d$, and
$$\operatorname{Tr}_{L/K}(\alpha) = -d\,c_{n-1}, \qquad N_{L/K}(\alpha) = \bigl((-1)^n c_0\bigr)^d.$$

*Proof.* First let $L = K(\alpha)$, so $d = 1$. Let $\chi$ be the characteristic polynomial of $\mu_\alpha$. It is monic of degree $n = [K(\alpha):K]$. By Cayley-Hamilton (Volume 7, Chapter 5), $\chi(\mu_\alpha) = 0$. Apply this map to $1 \in L$: $\chi(\mu_\alpha)(1) = \chi(\alpha) \cdot 1 = \chi(\alpha)$, since $\mu_\alpha^k(1) = \alpha^k$. So $\chi(\alpha) = 0$, and $m_\alpha$ divides $\chi$. Both are monic of degree $n$, so $\chi = m_\alpha$.

In general, let $\beta_1, \dots, \beta_d$ be a basis of $L$ over $K(\alpha)$. By the tower law, the elements $\alpha^i\beta_j$ with $0 \leq i < n$ form a basis of $L$ over $K$. The subspace $V_j$ spanned by $\beta_j, \alpha\beta_j, \dots, \alpha^{n-1}\beta_j$ is stable under $\mu_\alpha$, and $x \mapsto x\beta_j$ is an isomorphism $K(\alpha) \to V_j$ that commutes with $\mu_\alpha$. So the matrix of $\mu_\alpha$ is block diagonal, with $d$ blocks, each the matrix of $\mu_\alpha$ on $K(\alpha)$. The characteristic polynomial is $m_\alpha^d$.

For a monic $\chi$ of degree $N$, the trace is minus the coefficient of $X^{N-1}$, and the determinant is $(-1)^N\chi(0)$. For $\chi = m_\alpha^d$, the coefficient of $X^{nd-1}$ is $d\,c_{n-1}$, and $\chi(0) = c_0^d$. So $N(\alpha) = (-1)^{nd}c_0^d$. $\square$

**Corollary (Product and sum of conjugates).** In the setting of the theorem, suppose $m_\alpha = (X - \alpha_1)\cdots(X - \alpha_n)$ in some extension $E$ of $K$. Then
$$\operatorname{Tr}_{L/K}(\alpha) = d\,(\alpha_1 + \dots + \alpha_n), \qquad N_{L/K}(\alpha) = (\alpha_1 \cdots \alpha_n)^d.$$

*Proof.* Expand the product: $c_{n-1} = -(\alpha_1 + \dots + \alpha_n)$ and $c_0 = (-1)^n\alpha_1\cdots\alpha_n$. $\square$

The roots are counted with multiplicity. Chapter 3 constructs a field $E$ in which $m_\alpha$ splits.

::: mathlib
`Algebra.norm_eq_prod_roots` · `Mathlib.RingTheory.Norm.Transitivity`

For `hF : (map (algebraMap K F) (minpoly K x)).Splits`, the statement is `algebraMap K F (norm K x) = ((minpoly K x).aroots F).prod ^ finrank K⟮x⟯ L`. The power `finrank K⟮x⟯ L` is the $d$ of the theorem. The case $L = K(\alpha)$ with a power basis is `Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly : norm R pb.gen = (-1) ^ pb.dim * coeff 0`.

<?decl Algebra.norm_eq_prod_roots?>
:::

::: mathlib
`trace_eq_sum_roots` · `Mathlib.RingTheory.Trace.Basic`

The statement is `algebraMap K F (trace K L x) = finrank K⟮x⟯ L • ((minpoly K x).aroots F).sum`, under the same splitting hypothesis and `[FiniteDimensional K L]`. The coefficient forms are `PowerBasis.trace_gen_eq_nextCoeff_minpoly : trace K S pb.gen = -(minpoly K pb.gen).nextCoeff` and `trace_eq_finrank_mul_minpoly_nextCoeff`. Here `nextCoeff` is the coefficient $c_{n-1}$.

<?decl trace_eq_sum_roots?>
:::

**Theorem (Transitivity).** For finite extensions $K \subseteq E \subseteq L$, $N_{L/K} = N_{E/K} \circ N_{L/E}$ and $\operatorname{Tr}_{L/K} = \operatorname{Tr}_{E/K} \circ \operatorname{Tr}_{L/E}$.

The proof for the norm needs the determinant of a block matrix with commuting blocks, and this volume does not give it. In Mathlib it is `Algebra.trace_trace` and `Algebra.norm_norm`.

**Definition (Trace form).** For $L/K$ finite, the trace form is the symmetric bilinear form $(x, y) \mapsto \operatorname{Tr}_{L/K}(xy)$ on $L$.

Chapter 4 proves that the trace form is nondegenerate when $L/K$ is separable. In Mathlib it is `Algebra.traceForm`, and the result is `traceForm_nondegenerate`. For separable extensions the sums over roots become sums over embeddings into an algebraically closed field: `trace_eq_sum_embeddings` and `Algebra.norm_eq_prod_embeddings`.

### Examples

**Example (Quadratic fields).** Let $d \in \mathbb{Q}$ not be a square and $L = \mathbb{Q}(\sqrt d)$ with the basis $1, \sqrt d$. For $\alpha = a + b\sqrt d$, $\alpha \cdot 1 = a + b\sqrt d$ and $\alpha\sqrt d = bd + a\sqrt d$. So the matrix of $\mu_\alpha$ is
$$\begin{pmatrix} a & bd \\ b & a \end{pmatrix}, \qquad N(\alpha) = a^2 - db^2, \qquad \operatorname{Tr}(\alpha) = 2a.$$
The conjugates are $a \pm b\sqrt d$, with the product $a^2 - db^2$ and the sum $2a$. For $d = 2$, $N(1 + \sqrt 2) = -1$. The norm is multiplicative, so $N((1 + \sqrt 2)^k) = (-1)^k$. Each $(1 + \sqrt 2)^k$ lies in $\mathbb{Z}[\sqrt 2]$ with its inverse $(-1)^k(1 - \sqrt 2)^k$, so $\mathbb{Z}[\sqrt 2]$ has infinitely many units.

**Example (A cube root).** Let $c = \sqrt[3]{2}$ and $L = \mathbb{Q}(c)$, with $m_c = X^3 - 2$. Then $\operatorname{Tr}(c) = 0$ and $N(c) = (-1)^3 \cdot (-2) = 2$. The conjugates are $c, c\omega, c\omega^2$ with $\omega = e^{2\pi i/3}$, and $c^3\omega^3 = 2$ and $c(1 + \omega + \omega^2) = 0$ agree. Only the root $c$ is real, so by the theorem on embeddings, $\mathbb{Q}(c)$ has exactly one embedding into $\mathbb{R}$, and three into $\mathbb{C}$. For $\alpha = c^2$, the theorem with $d = 1$ applies to $m_{c^2} = X^3 - 4$, so $N(c^2) = 4 = N(c)^2$.

**Example (The trace form can vanish).** The nondegeneracy of the trace form needs separability. Let $K = \mathbb{F}_p(t)$ and $L = K(s)$ with $s^p = t$. Chapter 4 shows that $X^p - t$ is irreducible, so $[L:K] = p$ with the basis $1, s, \dots, s^{p-1}$. Then $\operatorname{Tr}(1) = p = 0$ in $K$. For $0 < i < p$, the element $s^i$ generates $L$, since $\gcd(i, p) = 1$, and it is a root of $X^p - t^i$. This polynomial is then its minimal polynomial, with $c_{p-1} = 0$, so $\operatorname{Tr}(s^i) = 0$. By linearity the trace is $0$ on all of $L$, and the trace form is $0$.

### The library around it

`Mathlib.FieldTheory.NormalizedTrace` defines `Algebra.normalizedTrace F K` in characteristic zero: the trace of $x$ from $F(x)$ to $F$, divided by $[F(x):F]$, which makes sense also for infinite algebraic extensions.

**Common errors of a learner.** The first error is to forget the exponent $d$: the norm of $\sqrt 2$ from $\mathbb{Q}(\sqrt 2, \sqrt 3)$ to $\mathbb{Q}$ is $(-2)^2 = 4$, not $-2$. The second error is to use `Algebra.norm` for an infinite extension: the junk value $1$ makes each statement trivial.

### Exercises

1. (A) Compute $N$ and $\operatorname{Tr}$ of $3 + 2\sqrt 5$ from $\mathbb{Q}(\sqrt 5)$ to $\mathbb{Q}$. Hint: the formula for quadratic fields.

2. (A) Find the conjugates of $\sqrt 2 + \sqrt 3$ over $\mathbb{Q}$ and over $\mathbb{Q}(\sqrt 2)$. Hint: the two minimal polynomials of Section 2.

3. (A) Compute $\operatorname{Tr}$ and $N$ of $1 + c$ from $\mathbb{Q}(\sqrt[3]{2})$ to $\mathbb{Q}$. Hint: $m_{1+c}(X) = m_c(X - 1)$.

4. (B) Show that $N_{L/K}(\alpha) \neq 0$ for $\alpha \neq 0$ using the minimal polynomial, not the inverse. Hint: $c_0 \neq 0$ since $m_\alpha$ is irreducible.

5. (B) How many $\mathbb{Q}$-embeddings does $\mathbb{Q}(\sqrt 2, \sqrt 3)$ have into $\mathbb{C}$? Hint: extend in two steps with the theorem on embeddings.

6. (B) Compute $N$ and $\operatorname{Tr}$ of $\sqrt 2$ and of $\sqrt 2 + \sqrt 3$ from $\mathbb{Q}(\sqrt 2, \sqrt 3)$ to $\mathbb{Q}$. Hint: $d = 2$ for $\sqrt 2$ and $d = 1$ for $\sqrt 2 + \sqrt 3$.

7. (B) Show that $x^2 - 2y^2 = 7$ has infinitely many integer solutions. Hint: $N(3 + \sqrt 2) = 7$ and multiply by powers of $3 + 2\sqrt 2$.

8. (B) Let $L/K$ be finite with $[L:K] = n$ nonzero in $K$. Show that $\operatorname{Tr}_{L/K}$ is surjective. Hint: $\operatorname{Tr}(a/n) = a$ for $a \in K$.

9. (C) Show that the units of $\mathbb{Z}[\sqrt 2]$ are the numbers $\pm(1 + \sqrt 2)^k$ with $k \in \mathbb{Z}$. Hint: for a unit $u > 1$, choose $k$ with $1 \leq u(1 + \sqrt 2)^{-k} < 1 + \sqrt 2$. For a unit $v = a + b\sqrt 2$ in this interval, the conjugate satisfies $|a - b\sqrt 2| = 1/v$, and this bounds $a$ and $b$.

### Notes and history

The norm and the trace come from the theory of algebraic numbers of the nineteenth century, where they were defined as the product and the sum of the conjugates. Mathlib defines them by the determinant, for each finite free algebra.

### Reference

<?reference?>
