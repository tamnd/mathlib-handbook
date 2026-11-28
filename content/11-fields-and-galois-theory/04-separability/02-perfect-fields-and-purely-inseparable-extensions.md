---
title: Perfect fields and purely inseparable extensions
kind: theory
modules:
  - Mathlib.FieldTheory.Perfect
  - Mathlib.FieldTheory.PerfectClosure
  - Mathlib.FieldTheory.IsPerfectClosure
  - Mathlib.FieldTheory.PurelyInseparable.Basic
  - Mathlib.FieldTheory.PurelyInseparable.Exponent
  - Mathlib.FieldTheory.PurelyInseparable.Tower
  - Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
  - Mathlib.FieldTheory.PurelyInseparable.AdjoinPthRoots
  - Mathlib.FieldTheory.SeparableClosure
  - Mathlib.FieldTheory.SeparableDegree
  - Mathlib.FieldTheory.IsSepClosed
  - Mathlib.FieldTheory.CardinalEmb
explains:
  E3: [PerfectRing, PerfectField, IsPurelyInseparable, separableClosure, Field.finSepDegree, Field.finSepDegree_mul_finInsepDegree]
  E2: [PerfectRing.bijective_frobenius, PerfectField.separable_of_irreducible, PerfectRing.toPerfectField, PerfectField.toPerfectRing, PerfectField.ofCharZero, PerfectField.ofFinite, Algebra.IsAlgebraic.isSeparable_of_perfectField, Algebra.IsAlgebraic.perfectField, PerfectField.separable_iff_squarefree, isPurelyInseparable_iff_pow_mem, IsPurelyInseparable.inseparable, IsPurelyInseparable.trans, mem_separableClosure_iff, separableClosure.isSeparable, separableClosure.isPurelyInseparable, Field.finInsepDegree, Field.Emb, Field.finSepDegree_eq_finrank_iff, Field.finSepDegree_le_finrank, Field.finSepDegree_mul_finSepDegree_of_isAlgebraic, IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree, Polynomial.natSepDegree, PerfectClosure, perfectClosure, IsSepClosed]
  E1: auto
families: []
requires: [V11.C03, V06.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Perfect fields and purely inseparable extensions

### Overview

Section 1 showed that inseparability needs characteristic $p$ and an element that is not a $p$th power, such as $t$ in $\mathbb{F}_p(t)$. A field in which each element is a $p$th power is perfect, and over a perfect field each algebraic extension is separable. Fields of characteristic $0$ and finite fields are perfect.

Over an imperfect field an algebraic extension $L/K$ has two layers. The separable elements form a field $K_s$, and over $K_s$ a $p^n$th power of each element lies in $K_s$: $L/K_s$ is purely inseparable. The degree splits as $[L:K] = [L:K]_s [L:K]_i$, where the separable degree $[L:K]_s$ counts the embeddings of $L$ over $K$ into an algebraic closure. This section proves these facts in the finite case.

The section uses the embeddings of a simple extension (Section 1), the algebraic closure and the extension of embeddings (Chapter 3), and the Frobenius map of Volume 6, Chapter 4.

### Definitions

**Definition (Perfect field).** A field $K$ is perfect if each irreducible polynomial over $K$ is separable.

In characteristic $p > 0$ the theorem below shows that this is the classical definition $K = K^p$. A field of characteristic $0$ is perfect by Section 1.

::: mathlib
`PerfectField` · `Mathlib.FieldTheory.Perfect`

The class `PerfectField K` has one field, `PerfectField.separable_of_irreducible`. Mathlib uses the definition by polynomials because it needs no characteristic. The instances `PerfectField.ofCharZero` and `PerfectField.ofFinite` cover the two common cases.

<?decl PerfectField?>
:::

::: mathlib
`PerfectRing` · `Mathlib.FieldTheory.Perfect`

The class `PerfectRing R p` says that `x ↦ x ^ p` is bijective (`PerfectRing.bijective_frobenius`). The two classes meet in `PerfectRing.toPerfectField` and the instance `PerfectField.toPerfectRing`, for a field of exponential characteristic `p`. The inverse of the Frobenius map is `frobeniusEquiv R p`.

<?decl PerfectRing?>
:::

**Definition (Purely inseparable extension).** Let $K$ have characteristic $p > 0$. An algebraic extension $L/K$ is purely inseparable if for each $\alpha \in L$ there is $n \ge 0$ with $\alpha^{p^n} \in K$. In characteristic $0$, $L/K$ is purely inseparable if $L = K$.

A root $\alpha$ of $X^{p^n} - a = (X - \alpha)^{p^n}$ is the only root of its minimal polynomial, so it is separable only if $\alpha \in K$. So only the elements of $K$ are both separable and purely inseparable.

::: mathlib
`IsPurelyInseparable` · `Mathlib.FieldTheory.PurelyInseparable.Basic`

The class `IsPurelyInseparable F E` is defined without the characteristic: `E` is integral over `F`, and each element of `E` that is separable over `F` lies in the image of `F` (`IsPurelyInseparable.inseparable`). The lemma `isPurelyInseparable_iff_pow_mem` gives the form above, with `q` the exponential characteristic, which is $1$ in characteristic $0$.

<?decl IsPurelyInseparable?>
:::

**Definition (Separable degree).** Let $L/K$ be a finite extension and $\Omega$ an algebraic closure of $L$. The separable degree $[L:K]_s$ is the number of $K$-embeddings $L \to \Omega$.

By the uniqueness of the algebraic closure (Chapter 3) the number does not depend on $\Omega$. For $K(\alpha)$, Section 1 shows that it is the number of distinct roots of the minimal polynomial of $\alpha$.

::: mathlib
`Field.finSepDegree` · `Mathlib.FieldTheory.SeparableDegree`

`Field.finSepDegree F E` is the number of elements of `Field.Emb F E`, the type of the `F`-algebra homomorphisms from `E` to `AlgebraicClosure E`, as a natural number. It is `0` when this type is infinite. For a simple extension, `IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree` identifies it with `(minpoly F α).natSepDegree`, the number of distinct roots.

<?decl Field.finSepDegree?>
:::

**Definition (Separable closure).** The separable closure of $K$ in $L$ is the set $K_s$ of the elements of $L$ that are separable over $K$. The theorem below shows that it is a field.

::: mathlib
`separableClosure` · `Mathlib.FieldTheory.SeparableClosure`

`separableClosure F E : IntermediateField F E`, with `mem_separableClosure_iff : x ∈ separableClosure F E ↔ IsSeparable F x`. The absolute notion, a separably closed field, is the class `IsSepClosed`.

<?decl separableClosure?>
:::

### Theorems and proofs

**Theorem (Perfect fields of characteristic $p$).** Let $K$ have characteristic $p > 0$. Then $K$ is perfect if and only if each element of $K$ is a $p$-th power.

*Proof.* Let $K = K^p$, and let $f$ be irreducible. Suppose that $f$ is not separable. By Section 1, $f = \sum_j a_j X^{jp}$. Choose $b_j$ with $b_j^p = a_j$. Since $x \mapsto x^p$ is a ring homomorphism of $K[X]$ in characteristic $p$,
$$f = \sum_j b_j^p (X^j)^p = \Bigl(\sum_j b_j X^j\Bigr)^p.$$
This is a factorization of $f$ into $p \ge 2$ nonconstant factors, which contradicts the irreducibility. So $f$ is separable.

Conversely let $a \in K$ be no $p$th power. As for $X^p - t$ in Section 1, $X^p - a$ is irreducible and not separable. So $K$ is not perfect. $\square$

**Corollary (Finite fields are perfect).** A finite field is perfect.

*Proof.* The Frobenius map of a finite field is an injective ring homomorphism, so it is surjective. $\square$

**Theorem (Algebraic extensions of a perfect field).** Let $K$ be perfect and $L/K$ algebraic. Then $L/K$ is separable, and $L$ is perfect.

*Proof.* Minimal polynomials are irreducible, so separable. For the second statement let $K$ have characteristic $p$, $\beta \in L$ and $M = K(\beta)$. First, $\beta \in K(\beta^p)$: $\beta$ is separable over $K(\beta^p)$ by Section 1, and its minimal polynomial divides $X^p - \beta^p = (X - \beta)^p$, so it is $X - \beta$.

The Frobenius map $\varphi$ of $M$ is an injective ring homomorphism, and $\varphi(M)$ is a subfield that contains $\varphi(K) = K$ and $\beta^p$. So $\varphi(M) \supseteq K(\beta^p) = M$, and $\beta = \gamma^p$ for some $\gamma \in M$. $\square$

::: mathlib
`Algebra.IsAlgebraic.isSeparable_of_perfectField` · `Mathlib.FieldTheory.Perfect`

The instance `[Algebra.IsAlgebraic K L] [PerfectField K] : Algebra.IsSeparable K L`. With it, the theorems of Chapter 5 that ask for separability apply over $\mathbb{Q}$ and $\mathbb{F}_p$ with no extra work. The second statement is `Algebra.IsAlgebraic.perfectField`.

<?decl Algebra.IsAlgebraic.isSeparable_of_perfectField?>
:::

**Theorem (Tower law for the separable degree).** Let $K \subseteq M \subseteq L$ be finite extensions. Then $[L:K]_s = [L:M]_s \, [M:K]_s$, and $[L:K]_s \le [L:K]$.

*Proof.* Fix an algebraic closure $\Omega$ of $L$; it is also one of $M$ and of $K$. A $K$-embedding $\sigma : M \to \Omega$ extends to an automorphism $\tilde\sigma$ of $\Omega$ (Chapter 3). A map $\rho : L \to \Omega$ extends $\sigma$ if and only if $\tilde\sigma^{-1} \circ \rho$ is an $M$-embedding, so $\sigma$ has exactly $[L:M]_s$ extensions. Each $K$-embedding of $L$ restricts to one of $M$, so $[L:K]_s = [M:K]_s \, [L:M]_s$.

For the inequality, use induction on $[L:K]$ with $M = K(\alpha)$, $\alpha \notin K$: Section 1 gives $[M:K]_s \le [M:K]$, induction gives $[L:M]_s \le [L:M]$, and the tower law (Chapter 1) finishes. $\square$

::: mathlib
`Field.finSepDegree_mul_finSepDegree_of_isAlgebraic` · `Mathlib.FieldTheory.SeparableDegree`

The tower law `finSepDegree F E * finSepDegree E K = finSepDegree F K` for `K / E` algebraic. The inequality is `Field.finSepDegree_le_finrank`, and the case of equality is `Field.finSepDegree_eq_finrank_iff`. The number of distinct roots of a polynomial is `Polynomial.natSepDegree`.

<?decl Field.finSepDegree_mul_finSepDegree_of_isAlgebraic?>
:::

**Theorem (Separable degree and separability).** Let $L/K$ be finite. Then $[L:K]_s = [L:K]$ if and only if $L/K$ is separable. If $L = K(\alpha_1, \dots, \alpha_r)$ with each $\alpha_i$ separable over $K$, then $L/K$ is separable.

*Proof.* Let $L/K$ be separable, and use induction as above: $[M:K]_s = [M:K]$ by Section 1, and $L/M$ is separable, so $[L:M]_s = [L:M]$.

Conversely let $[L:K]_s = [L:K]$, and let $\gamma \in L$, $M = K(\gamma)$. Then
$$[L:K] = [L:K]_s = [L:M]_s [M:K]_s \le [L:M] [M:K]_s.$$
Divide by $[L:M]$: $[M:K] \le [M:K]_s$, so equality holds, the minimal polynomial of $\gamma$ has distinct roots, and $\gamma$ is separable.

For the last statement, put $L_i = K(\alpha_1, \dots, \alpha_i)$. Since $\alpha_{i+1}$ is separable over $L_i$, $[L_{i+1} : L_i]_s = [L_{i+1}:L_i]$. Multiply along the tower and use the first part. $\square$

**Corollary (The separable closure is a field).** Let $L/K$ be algebraic. The set $K_s$ of separable elements is a subfield of $L$ that contains $K$.

*Proof.* Let $\alpha, \beta \in K_s$. By the theorem, $K(\alpha, \beta)/K$ is separable. So $\alpha \pm \beta$, $\alpha\beta$ and $\alpha/\beta$ (for $\beta \neq 0$) are separable. $\square$

**Theorem (The two layers).** Let $L/K$ be a finite extension in characteristic $p$, and $K_s$ the separable closure of $K$ in $L$. Then $L/K_s$ is purely inseparable, and $[L:K] = [L:K]_s \, [L:K_s]$, with $[L:K]_s = [K_s:K]$.

*Proof.* Let $\alpha \in L$ with minimal polynomial $f$ over $K$. By Section 1, $f = g(X^{p^e})$ with $g$ separable and irreducible. Then $g(\alpha^{p^e}) = 0$, so $\alpha^{p^e}$ is separable over $K$ and lies in $K_s$. So $L/K_s$ is purely inseparable.

A $K_s$-embedding $\tau$ of $L$ sends $\alpha$ to a root of $(X - \alpha)^{p^n}$, so $\tau$ is the identity and $[L:K_s]_s = 1$. By the tower law and the previous theorem, $[L:K]_s = [K_s:K]_s = [K_s:K]$, and $[L:K] = [L:K_s][K_s:K] = [L:K_s] [L:K]_s$. $\square$

The number $[L:K]_i = [L:K_s]$ is the inseparable degree. It is a power of $p$, since each step $K_s(\alpha^{p^{k+1}}) \subseteq K_s(\alpha^{p^k})$ has degree $1$ or $p$.

::: mathlib
`Field.finSepDegree_mul_finInsepDegree` · `Mathlib.FieldTheory.PurelyInseparable.Basic`

The equality `finSepDegree F E * finInsepDegree F E = finrank F E`, where `Field.finInsepDegree F E` is the degree of `E` over `separableClosure F E`. The layers are the instances `separableClosure.isSeparable` and `separableClosure.isPurelyInseparable`. The infinite version, with cardinals, is `Field.sepDegree_mul_insepDegree`.

<?decl Field.finSepDegree_mul_finInsepDegree?>
:::

### Examples

**Example (An imperfect field).** The field $\mathbb{F}_p(t)$ is not perfect, since $t$ is not a $p$-th power (Section 1). Its subfield $\mathbb{F}_p(t^p)$ is the image of the Frobenius map. The extension $\mathbb{F}_p(t)/\mathbb{F}_p(t^p)$ is purely inseparable of degree $p$, with separable degree $1$. So the hypothesis "perfect" in the theorem on algebraic extensions is needed.

**Example (Both layers).** Let $p$ be odd, $K = \mathbb{F}_p(t)$ and $L = K(u)$ with $u^{2p} = t$. The polynomial $X^{2p} - t$ is Eisenstein at $t$ (Chapter 2), so $[L:K] = 2p$. It is $g(X^p)$ with $g = X^2 - t$ separable, since $p \neq 2$. So $K_s \supseteq K(u^p) = K(\sqrt t)$, and $L/K(u^p)$ is purely inseparable of degree $p$, since $u$ is a root of $X^p - u^p$. So $[L:K]_s = 2$, $[L:K]_i = p$ and $K_s = K(\sqrt t)$. The two $K$-embeddings send $u$ to $u$ and to $-u$, the two distinct roots of $X^{2p} - t = (X^2 - u^2)^p$.

### The library around it

Mathlib has two perfect closures. `PerfectClosure K p` is the absolute one, a direct limit of copies of $K$ along the Frobenius map. `perfectClosure F E` is the relative one, the elements $x$ with $x^{p^n} \in F$ for some $n$. The class `IsPerfectClosure` characterizes the absolute one by a universal property. In the same way `separableClosure F E` is relative, and `IsSepClosed` gives the absolute notion. The files `Mathlib.FieldTheory.PurelyInseparable.Tower` and `Mathlib.FieldTheory.PurelyInseparable.Exponent` prove the tower laws for the inseparable degree, with `IsPurelyInseparable.trans`. Over a perfect field, `PerfectField.separable_iff_squarefree` says that a polynomial is separable if and only if it is squarefree. The reference table lists the declarations of the section.

The module `Mathlib.FieldTheory.CardinalEmb` counts the embeddings of an infinite algebraic extension. For a finite separable extension, the number of elements of `Field.Emb F E` is the degree. For an infinite one the count jumps: if $E/F$ is algebraic and separable of infinite degree, then `Field.Emb.cardinal_eq_two_pow_rank` gives $|\mathrm{Emb}_F(E)| = 2^{[E:F]}$. More generally, `Field.Emb.cardinal_eq_two_pow_sepDegree` gives $2^{\mathrm{sepDeg}(E/F)}$ for an algebraic extension whose separable degree `Field.sepDegree F E` is infinite, and `Field.Emb.cardinal_eq` combines the finite and the infinite case in one formula. The proof is a transfinite recursion along a well ordered basis: at each step of the recursion, an embedding of the field so far extends in at least two ways. For example, the algebraic closure of $\mathbb{Q}$ has $2^{\aleph_0}$ embeddings into itself over $\mathbb{Q}$.

### Exercises

1. (A) Show that $\mathbb{F}_p(t^p)$ is the set of $p$-th powers of $\mathbb{F}_p(t)$.
2. (A) Show that an algebraically closed field is perfect.
3. (A) Let $L/K$ be both separable and purely inseparable. Show that $L = K$.
4. (B) Let $K$ be perfect of characteristic $p$. Show that $X^{p^n} - a$ factors as $(X - b)^{p^n}$ over $K$ for each $a \in K$.
5. (B) Compute $[L:K]_s$ and $[L:K]_i$ for $K = \mathbb{F}_p(t)$ and $L = K(t^{1/p^2})$.
6. (B) Let $L/K$ be finite and purely inseparable of characteristic $p$. Show that $[L:K]$ is a power of $p$.
7. (C) Let $K = \mathbb{F}_p(s, t)$. Show that $K/K^p$ has degree $p^2$, and that it is not a simple extension: each element $\gamma$ of $K$ has $\gamma^p \in K^p$, so $[K^p(\gamma) : K^p] \le p$.

### Notes and history

Steinitz introduced perfect fields and the decomposition of an algebraic extension into a separable and a purely inseparable part in his paper of 1910.

### Reference

<?reference?>
