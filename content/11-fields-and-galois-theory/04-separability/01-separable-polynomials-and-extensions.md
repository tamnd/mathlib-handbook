---
title: Separable polynomials and separable extensions
kind: theory
modules:
  - Mathlib.FieldTheory.Separable
  - Mathlib.FieldTheory.SeparablyGenerated
  - Mathlib.FieldTheory.TranscendentalSeparable
explains:
  E3: [Polynomial.Separable, Polynomial.separable_iff_derivative_ne_zero, Irreducible.separable, IsSeparable, Algebra.IsSeparable, AlgHom.card_of_powerBasis]
  E2: [Polynomial.separable_def, Polynomial.nodup_roots, Polynomial.nodup_roots_iff_of_splits, Polynomial.rootMultiplicity_le_one_of_separable, Polynomial.Separable.of_dvd, Polynomial.Separable.map, Polynomial.separable_map, Polynomial.Separable.squarefree, Polynomial.exists_separable_of_irreducible, Polynomial.isUnit_or_eq_zero_of_separable_expand, Polynomial.separable_X_pow_sub_C, Polynomial.X_pow_sub_one_separable_iff, Polynomial.card_rootSet_eq_natDegree, IsSeparable.tower_top, Algebra.isSeparable_tower_top_of_isSeparable, Algebra.isSeparable_tower_bot_of_isSeparable, Algebra.IsSeparable.of_algHom, IsSeparable.isIntegral]
  E1: auto
families: []
requires: [V11.C03, V06.C04, V06.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Separable polynomials and separable extensions

### Overview

A polynomial $f$ of degree $n$ over a field $K$ splits in a splitting field $L$ as $f = c \prod_{i=1}^n (X - \alpha_i)$. When the roots $\alpha_i$ are distinct, $f$ is separable. Galois theory needs this case: the automorphisms of $L$ over $K$ permute the roots, and their number is controlled by the number of distinct roots.

This section gives a test inside $K[X]$: $f$ is separable if and only if $f$ and its formal derivative $f'$ are coprime. For an irreducible $f$ the test becomes $f' \neq 0$. So each irreducible polynomial is separable in characteristic $0$, and in characteristic $p$ an irreducible polynomial is inseparable only if it is a polynomial in $X^p$. The section then defines separable elements and extensions, and proves that a simple extension $K(\alpha)$ of degree $n$ has exactly $n$ embeddings over $K$ into a field where the minimal polynomial splits if and only if $\alpha$ is separable.

The section uses the splitting fields of Chapter 3, the minimal polynomial of Chapter 2, and the characteristic of Volume 6, Chapter 4.

### Definitions

**Definition (Formal derivative).** Let $R$ be a commutative ring and $f = \sum_{k=0}^n a_k X^k \in R[X]$. The formal derivative of $f$ is $f' = \sum_{k=1}^n k a_k X^{k-1}$.

The map $f \mapsto f'$ is $R$-linear and satisfies the product rule $(fg)' = f'g + fg'$, as a check on monomials shows. In characteristic $p$, $(X^p)' = p X^{p-1} = 0$, so a nonconstant polynomial can have the derivative $0$.

::: mathlib
`Polynomial.derivative` · `Mathlib.Algebra.Polynomial.Derivative`

The formal derivative as a linear map `R[X] →ₗ[R] R[X]`, over a semiring. The product rule is `Polynomial.derivative_mul`. Its home is the volume on polynomials.

<?decl Polynomial.derivative?>
:::

**Definition (Separable polynomial).** A polynomial $f \in R[X]$ is separable if $f$ and $f'$ are coprime: there are $a, b \in R[X]$ with $a f + b f' = 1$.

Over a field $K$, this holds if and only if $\gcd(f, f') = 1$ (Volume 6, Chapter 6). The Bezout form does not change when $K$ is replaced by a larger field: the identity $a f + b f' = 1$ in $K[X]$ is also an identity in $L[X]$.

::: mathlib
`Polynomial.Separable` · `Mathlib.FieldTheory.Separable`

The predicate `f.Separable`, defined as `IsCoprime f (derivative f)` over a commutative semiring; `Polynomial.separable_def` unfolds it. Mathlib does not define separability by distinct roots, since the roots live in another field. The zero polynomial is not separable, and a nonzero constant is separable.

<?decl Polynomial.Separable?>
:::

**Definition (Separable element, separable extension).** Let $L/K$ be an extension. An element $\alpha \in L$ is separable over $K$ if it is algebraic over $K$ and its minimal polynomial $m_\alpha$ over $K$ is separable. The extension $L/K$ is separable if each element of $L$ is separable over $K$.

A separable extension is algebraic by definition. Mathlib also has files on separably generated transcendental extensions, which this volume does not use.

::: mathlib
`IsSeparable` · `Mathlib.FieldTheory.Separable`

`IsSeparable K x` means `(minpoly K x).Separable`. The junk value of `minpoly` does the work of the hypothesis "algebraic": if `x` is transcendental, `minpoly K x = 0`, and `0` is not separable. The lemma `IsSeparable.isIntegral` extracts that `x` is integral.

<?decl IsSeparable?>
:::

::: mathlib
`Algebra.IsSeparable` · `Mathlib.FieldTheory.Separable`

The class `Algebra.IsSeparable K L` says `∀ x : L, IsSeparable K x`. The instance `Algebra.IsSeparable.isAlgebraic` gives `Algebra.IsAlgebraic K L`, and Section 2 gives an instance for each algebraic extension of a perfect field.

<?decl Algebra.IsSeparable?>
:::

### Theorems and proofs

**Theorem (Separable means distinct roots).** Let $f \in K[X]$ be nonzero, and let $L/K$ be an extension in which $f$ splits. Then $f$ is separable if and only if the roots of $f$ in $L$ are distinct.

*Proof.* First let $f$ be separable, so $a f + b f' = 1$ in $L[X]$. Suppose that $\alpha$ is a root of multiplicity at least $2$. Then $f = (X - \alpha)^2 g$ for some $g \in L[X]$. The product rule gives $f' = 2(X - \alpha) g + (X - \alpha)^2 g'$, so $f'(\alpha) = 0$. Evaluate the identity at $\alpha$: $a(\alpha) \cdot 0 + b(\alpha) \cdot 0 = 1$, a contradiction.

Conversely let the roots be distinct, and suppose that $d = \gcd(f, f')$ is not constant. Since $d \mid f$ and $f$ splits in $L$, $d$ has a root $\alpha \in L$, so $f(\alpha) = f'(\alpha) = 0$. Write $f = (X - \alpha) g$; then $f' = g + (X - \alpha) g'$, so $g(\alpha) = 0$ and $(X - \alpha)^2 \mid f$, a contradiction. So $d = 1$. $\square$

So $\alpha$ is a multiple root of $f$ if and only if $f(\alpha) = f'(\alpha) = 0$.

::: mathlib
`Polynomial.nodup_roots_iff_of_splits` · `Mathlib.FieldTheory.Separable`

For a nonzero `f` that splits over its own field, `f.roots.Nodup ↔ f.Separable`. For a splitting field `L`, apply it to `f.map (algebraMap K L)` and use `Polynomial.separable_map`. The direction from separable to distinct roots holds over each domain: `Polynomial.nodup_roots`.

<?decl Polynomial.nodup_roots_iff_of_splits?>
:::

**Theorem (Irreducible polynomials).** Let $f \in K[X]$ be irreducible. Then $f$ is separable if and only if $f' \neq 0$.

*Proof.* Since $f$ is irreducible, $d = \gcd(f, f')$ is $1$ or $f$ up to a unit. If $f' \neq 0$, then $\deg f' < \deg f$, so $f \nmid f'$ and $d = 1$. If $f' = 0$, then $d$ is $f$, which is not constant. $\square$

::: mathlib
`Polynomial.separable_iff_derivative_ne_zero` · `Mathlib.FieldTheory.Separable`

The statement `Irreducible f → (f.Separable ↔ derivative f ≠ 0)` over a field.

<?decl Polynomial.separable_iff_derivative_ne_zero?>
:::

**Corollary (Characteristic zero).** If $K$ has characteristic $0$, each irreducible polynomial over $K$ is separable, and each algebraic extension of $K$ is separable.

*Proof.* If $f$ is irreducible of degree $n \geq 1$ with leading coefficient $a_n$, the coefficient of $X^{n-1}$ in $f'$ is $n a_n \neq 0$. So $f' \neq 0$. Minimal polynomials are irreducible. $\square$

::: mathlib
`Irreducible.separable` · `Mathlib.FieldTheory.Separable`

The statement `Irreducible f → f.Separable` under `[CharZero F]`. The instance that makes each algebraic extension of a field of characteristic $0$ separable goes through the class `PerfectField` of Section 2.

<?decl Irreducible.separable?>
:::

**Theorem (Characteristic $p$).** Let $K$ have characteristic $p > 0$ and let $f \in K[X]$ be irreducible. Then $f' = 0$ if and only if $f = g(X^p)$ for some $g \in K[X]$. In general there are $e \ge 0$ and a separable irreducible $g$ with $f = g(X^{p^e})$.

*Proof.* Write $f = \sum_k a_k X^k$. Then $f' = \sum_k k a_k X^{k-1}$ is $0$ if and only if $k a_k = 0$ for each $k$, that is, $a_k = 0$ for each $k$ that is not divisible by $p$. That is the statement $f = \sum_j a_{jp} X^{jp} = g(X^p)$ with $g = \sum_j a_{jp} X^j$.

For the second statement use induction on $\deg f$. If $f' \neq 0$, take $e = 0$. If $f' = 0$, write $f = g_1(X^p)$. A factorization $g_1 = uv$ gives $f = u(X^p) v(X^p)$, so $g_1$ is irreducible, and $\deg g_1 < \deg f$. The induction gives $g_1 = g(X^{p^{e_1}})$ and $f = g(X^{p^{e_1 + 1}})$. $\square$

::: mathlib
`Polynomial.exists_separable_of_irreducible` · `Mathlib.FieldTheory.Separable`

The decomposition `∃ n g, g.Separable ∧ expand F (p ^ n) g = f` for an irreducible `f` in characteristic `p ≠ 0`; `Polynomial.expand F q` substitutes `X ^ q` for `X`. By `Polynomial.isUnit_or_eq_zero_of_separable_expand`, `expand F (p ^ n) f` is separable only when `n = 0` or `f` is a unit.

<?decl Polynomial.exists_separable_of_irreducible?>
:::

**Theorem (Towers).** Let $K \subseteq E \subseteq L$ be fields and $\alpha \in L$ separable over $K$. Then $\alpha$ is separable over $E$. So if $L/K$ is separable, then $L/E$ and $E/K$ are separable.

*Proof.* The minimal polynomial $m_E$ of $\alpha$ over $E$ divides $m_K$ (Chapter 2). A divisor of a separable polynomial is separable: from $m_K = m_E h$ and $a m_K + b m_K' = 1$ follows $(a h + b h') m_E + (b h) m_E' = 1$. For $E/K$, the minimal polynomial over $K$ of an element of $E$ does not depend on the field that contains it. $\square$

The converse, that $L/E$ and $E/K$ separable imply $L/K$ separable, is also true; it follows from the separable degree in Section 2.

::: mathlib
`IsSeparable.tower_top` · `Mathlib.FieldTheory.Separable`

The statement `IsSeparable F x → IsSeparable L x` for a tower `F → L → E` with `[IsScalarTower F L E]`. The versions for the whole extension are `Algebra.isSeparable_tower_top_of_isSeparable` and `Algebra.isSeparable_tower_bot_of_isSeparable`. The divisor step is `Polynomial.Separable.of_dvd`.

<?decl IsSeparable.tower_top?>
:::

**Theorem (Embeddings of a simple extension).** Let $\alpha$ be algebraic over $K$ with minimal polynomial $m$ of degree $n$, and let $\Omega$ be an extension of $K$ in which $m$ splits. The $K$-embeddings $K(\alpha) \to \Omega$ are in bijection with the distinct roots of $m$ in $\Omega$. So there are at most $n$ of them, and there are exactly $n$ if and only if $\alpha$ is separable over $K$.

*Proof.* A $K$-embedding $\sigma$ is determined by $\sigma(\alpha)$, since $K(\alpha)$ consists of polynomials in $\alpha$ (Chapter 2), and $m(\sigma(\alpha)) = \sigma(m(\alpha)) = 0$. So $\sigma \mapsto \sigma(\alpha)$ maps the embeddings injectively to the roots.

It is surjective: for a root $\beta$, evaluation at $\beta$ kills $(m)$ and gives $K(\alpha) \cong K[X]/(m) \to \Omega$ with $\alpha \mapsto \beta$.

The $n$ roots of $m$ in $\Omega$, counted with multiplicity, are distinct if and only if $m$ is separable. $\square$

::: mathlib
`AlgHom.card_of_powerBasis` · `Mathlib.FieldTheory.Separable`

For a power basis `pb` of `S` over `K` with separable generator, and a field `L` in which the minimal polynomial splits, `Fintype.card (S →ₐ[K] L) = pb.dim`. The count of roots is `Polynomial.card_rootSet_eq_natDegree`.

<?decl AlgHom.card_of_powerBasis?>
:::

### Examples

**Example (An inseparable irreducible polynomial).** Let $K = \mathbb{F}_p(t)$ and $f = X^p - t$. Then $f' = 0$, so $f$ is not separable, although it is irreducible. So the corollary needs characteristic $0$.

For the irreducibility, let $s$ be a root in a splitting field. Then $(X - s)^p = X^p - t$ (Volume 6, Chapter 4). A monic factor of degree $k$, $0 < k < p$, is $(X - s)^k$, whose coefficient $-ks$ lies in $K$, so $s \in K$. But $t$ is not a $p$th power in $K$: $t b^p = a^p$ with $a, b \in \mathbb{F}_p[t]$ gives $1 + p \deg b = p \deg a$, false modulo $p$.

**Example ($X^n - 1$).** Let $n \neq 0$ in $K$ and $f = X^n - 1$. Then $\tfrac{1}{n} X \cdot f' - f = 1$, so $f$ is separable and has $n$ distinct roots, the $n$th roots of unity of Chapter 8. Over $\mathbb{Q}$ the three embeddings of $\mathbb{Q}(\sqrt[3]{2})$ into $\mathbb{C}$ send $\sqrt[3]{2}$ to its three distinct complex conjugates. If $K$ has characteristic $p$ and $n = pm$, then $X^n - 1 = (X^m - 1)^p$ is not separable. Mathlib has both cases in `Polynomial.X_pow_sub_one_separable_iff`.

### The library around it

The file `Mathlib.FieldTheory.Separable` has three layers. For polynomials over a commutative ring: `Polynomial.Separable` and its stability (`Polynomial.Separable.of_dvd`, `Polynomial.Separable.map`, `Polynomial.Separable.squarefree`, `Polynomial.rootMultiplicity_le_one_of_separable`). For polynomials over a field: the derivative test, `Polynomial.separable_X_pow_sub_C`, and the expansion lemmas. For elements and algebras: `IsSeparable`, `Algebra.IsSeparable`, the tower lemmas, and `Algebra.IsSeparable.of_algHom`. The files `Mathlib.FieldTheory.SeparablyGenerated` and `Mathlib.FieldTheory.TranscendentalSeparable` treat transcendental extensions. The reference table lists the declarations of the section.

### Exercises

1. (A) Decide which of these polynomials are separable: $X^3 - 3X + 2$ over $\mathbb{Q}$, $X^3 + X + 1$ over $\mathbb{F}_2$, $X^4 + 1$ over $\mathbb{F}_2$. Hint: compute $\gcd(f, f')$.
2. (A) Show that a product $fg$ of separable polynomials over a field is separable if and only if $f$ and $g$ are coprime.
3. (B) Let $K$ have characteristic $p$ and $a \in K$. Show that $X^p - X - a$ is separable. Hint: its derivative is $-1$.
4. (B) Let $K$ have characteristic $p$, and let $\alpha$ be algebraic over $K$. Show that $\alpha$ is separable over $K$ if $K(\alpha) = K(\alpha^p)$. Hint: write the minimal polynomial as $g(X^{p^e})$.
5. (B) Count the $\mathbb{Q}$-embeddings of $\mathbb{Q}(\sqrt 2 + i)$ into $\mathbb{C}$. Hint: find the minimal polynomial, of degree $4$.
6. (C) Let $K = \mathbb{F}_p(t)$ and $f = X^{p^2} - t$. Show that $f$ has one root $s$ in a splitting field, of multiplicity $p^2$, and that $f$ is irreducible over $K$. Find $e$ and $g$ with $f = g(X^{p^e})$ and $g$ separable. Hint: a monic factor is $(X - s)^k$; write $k = p^a u$ with $p \nmid u$, so $(X - s)^k = (X^{p^a} - s^{p^a})^u$, and look at the coefficient of $X^{p^a(u-1)}$.

### Notes and history

The words separable and inseparable are due to Steinitz, in his paper of 1910 on the algebraic theory of fields, which first treated positive characteristic systematically. Before that, Galois theory was a theory of subfields of $\mathbb{C}$, where the question does not arise.

### Reference

<?reference?>
