---
title: Derivatives, multiple roots and adjoining a root
kind: theory
modules:
  - Mathlib.RingTheory.Polynomial.Radical
  - Mathlib.RingTheory.Polynomial.SeparableDegree
  - Mathlib.RingTheory.Polynomial.Wronskian
  - Mathlib.RingTheory.Polynomial.Nilpotent
explains:
  E3: [Polynomial.derivative, Polynomial.one_lt_rootMultiplicity_iff_isRoot, AdjoinRoot, AdjoinRoot.lift]
  E2: [Polynomial.derivative_mul, Polynomial.derivative_X_pow, Polynomial.derivative_pow, Polynomial.derivative_comp, Polynomial.rootMultiplicity, Polynomial.le_rootMultiplicity_iff, Polynomial.rootMultiplicity_pos, Polynomial.derivative_rootMultiplicity_of_root, Polynomial.isRoot_of_isRoot_of_dvd_derivative_mul, AdjoinRoot.mk, AdjoinRoot.root, AdjoinRoot.of, AdjoinRoot.mk_eq_zero, AdjoinRoot.isRoot_root, AdjoinRoot.lift_root, AdjoinRoot.instField, AdjoinRoot.powerBasis, AdjoinRoot.liftAlgHom, AdjoinRoot.of.injective_of_degree_ne_zero]
  E1: [Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_add, Polynomial.rootMultiplicity_eq_zero, Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative, AdjoinRoot.mk_self, AdjoinRoot.mk_surjective, AdjoinRoot.algHom_ext, AdjoinRoot.span_maximal_of_irreducible, AdjoinRoot.induction_on, Polynomial.Separable, Polynomial.Separable.squarefree, PerfectField.separable_iff_squarefree]
families: []
requires: [V06.C05, V06.C06, V09.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Derivatives, multiple roots and adjoining a root

### Overview

The rule $X^n \mapsto n X^{n-1}$ defines a derivative over every commutative ring, and this section uses it to detect multiple roots and repeated factors. The second half builds roots that do not exist yet: the quotient $R[X]/(f)$ contains a root of $f$, the class of $X$. This is Kronecker's construction, and it gives a field when $R$ is a field and $f$ is irreducible.

### Definitions

Let $R$ be a commutative ring.

**Definition (Formal derivative).** The derivative of $f = \sum_{i = 0}^n a_i X^i \in R[X]$ is $f' = \sum_{i = 1}^{n} i a_i X^{i-1}$.

The map $f \mapsto f'$ is $R$-linear, $c' = 0$ for a constant $c$, and $X' = 1$.

**Definition (Multiplicity of a root).** Let $f \in R[X]$ be nonzero and $a \in R$. The multiplicity of $a$ in $f$ is the largest $m \ge 0$ with $(X - a)^m \mid f$. A root of multiplicity at least $2$ is a multiple root, and a root of multiplicity $1$ is a simple root.

The multiplicity is at most $\deg f$, since $X - a$ is monic. By the factor theorem (Volume 6, Chapter 5), $a$ is a root exactly when its multiplicity is at least $1$.

::: mathlib
`Polynomial.derivative` · `Mathlib.Algebra.Polynomial.Derivative`

`derivative : R[X] →ₗ[R] R[X]` is a linear map, so additivity is `map_add`. The rules are `derivative_C`, `derivative_X`, `derivative_X_pow`, `derivative_mul`, `derivative_pow` and the chain rule `derivative_comp`. The factor `i` is computed in `R`, so `derivative (X ^ p) = 0` over `ZMod p`.

<?decl Polynomial.derivative?>
:::

::: mathlib
`Polynomial.rootMultiplicity` · `Mathlib.Algebra.Polynomial.Div`

`rootMultiplicity a f : ℕ` has the junk value `0` at `f = 0`. `le_rootMultiplicity_iff` says `n ≤ rootMultiplicity a f ↔ (X - C a) ^ n ∣ f` for `f ≠ 0`, and `rootMultiplicity_pos` locates the roots.

<?decl Polynomial.rootMultiplicity?>
:::

### Theorems and proofs

**Theorem (Leibniz rule).** For $f, g \in R[X]$, $(fg)' = f'g + fg'$. Hence $(f^n)' = n f^{n-1} f'$ for $n \ge 1$.

*Proof.* Both sides are $R$-bilinear in $(f, g)$, so it suffices to check monomials $f = X^i$, $g = X^j$. Both sides are $(i + j) X^{i+j-1}$, with the convention that $0 \cdot X^{-1} = 0$. The power rule follows by induction on $n$: $(f^{n+1})' = (f^n f)' = n f^{n-1} f' f + f^n f' = (n + 1) f^n f'$. $\square$

**Theorem (Multiple roots).** Let $f \in R[X]$ and $a \in R$. Then $(X - a)^2 \mid f$ if and only if $f(a) = 0$ and $f'(a) = 0$.

*Proof.* If $f = (X - a)^2 h$, then $f(a) = 0$, and $f' = 2(X - a) h + (X - a)^2 h'$ by the Leibniz rule, so $f'(a) = 0$. Conversely, let $f(a) = 0$. By the factor theorem $f = (X - a) g$ for some $g \in R[X]$. Then $f' = g + (X - a) g'$, so $g(a) = f'(a) = 0$. By the factor theorem again $g = (X - a) h$, and $f = (X - a)^2 h$. $\square$

**Theorem (Multiplicity in characteristic $0$).** Let $R$ be a domain of characteristic $0$, $f \in R[X]$ nonzero, and $a$ a root of $f$ of multiplicity $m \ge 1$. Then $a$ is a root of $f'$ of multiplicity exactly $m - 1$.

*Proof.* Write $f = (X - a)^m g$ with $g(a) \ne 0$. Such a $g$ exists: if $g(a) = 0$, then $(X - a)^{m+1} \mid f$. The Leibniz rule gives
$$f' = m (X - a)^{m-1} g + (X - a)^m g' = (X - a)^{m-1} \bigl( m g + (X - a) g' \bigr).$$
The second factor takes the value $m \, g(a)$ at $a$. This is nonzero, since $m \ne 0$ in $R$ and $R$ is a domain. So $(X - a)^{m-1}$ divides $f'$ and $(X - a)^m$ does not. $\square$

**Theorem (Square factors).** Let $k$ be a field and $f \in k[X]$ nonzero.

1. If $\gcd(f, f') = 1$, then $f$ is squarefree: no $g$ of positive degree has $g^2 \mid f$.
2. If $k$ has characteristic $0$ and $f$ is squarefree, then $\gcd(f, f') = 1$.

*Proof.* (1) Suppose $f = g^2 h$ with $\deg g \ge 1$. Then $f' = g (2 g' h + g h')$, so $g$ divides $\gcd(f, f')$.

(2) Suppose that $\gcd(f, f') \ne 1$. It has an irreducible factor $q$, which divides $f$ and $f'$. Write $f = q h$. Since $f$ is squarefree, $q \nmid h$. The Leibniz rule gives $f' = q' h + q h'$, so $q \mid q' h$. The element $q$ is prime in $k[X]$, and $q \nmid h$, so $q \mid q'$. In characteristic $0$ the leading term $n c X^{n-1}$ of $q'$, with $n = \deg q$, is nonzero, so $q' \ne 0$ has smaller degree than $q$ and $q \nmid q'$, a contradiction. $\square$

::: mathlib
`Polynomial.one_lt_rootMultiplicity_iff_isRoot` · `Mathlib.Algebra.Polynomial.FieldDivision`

For `f ≠ 0` it states `1 < rootMultiplicity t f ↔ f.IsRoot t ∧ (derivative f).IsRoot t`. The theorem in characteristic $0$ is `derivative_rootMultiplicity_of_root`, under `[CharZero R]`. The polynomials with $\gcd(f, f') = 1$ are the separable ones, `Polynomial.Separable`, defined by `IsCoprime f (derivative f)`, and Volume 11 studies them.

<?decl Polynomial.one_lt_rootMultiplicity_iff_isRoot?>
:::

**Definition (Adjoining a root).** Let $f \in R[X]$. The ring $R[X]/(f)$ is written $R[\alpha]$, where $\alpha$ is the class of $X$. The map $R \to R[X]/(f)$ sends $r$ to the class of the constant $r$.

**Theorem (Kronecker).** Let $f \in R[X]$ and $A = R[X]/(f)$ with $\alpha$ the class of $X$.

1. $f(\alpha) = 0$ in $A$.
2. Universal property: for a ring homomorphism $i \colon R \to S$ and $s \in S$ with $\sum i(a_j) s^j = 0$, there is exactly one ring homomorphism $\varphi \colon A \to S$ with $\varphi(r) = i(r)$ for $r \in R$ and $\varphi(\alpha) = s$.
3. If $f$ is monic of degree $n \ge 1$, then $R \to A$ is injective, and each element of $A$ is $b_0 + b_1 \alpha + \dots + b_{n-1} \alpha^{n-1}$ with unique $b_j \in R$.
4. If $R = k$ is a field and $f$ is irreducible, then $A$ is a field, and $[A : k] = \deg f$.

*Proof.* (1) The class of $f(X)$ is $f(\alpha)$, since reduction is a ring homomorphism, and $f \in (f)$.

(2) The universal property of $R[X]$ gives a unique ring homomorphism $\psi \colon R[X] \to S$ with $\psi|_R = i$ and $\psi(X) = s$. Then $\psi(f) = \sum i(a_j) s^j = 0$, so $(f) \subseteq \ker \psi$, and $\psi$ factors through $A$. Uniqueness: $A$ is generated as a ring by the image of $R$ and $\alpha$.

(3) Division by the monic $f$ (Volume 6, Chapter 5) writes each $g \in R[X]$ as $g = qf + r$ with $\deg r < n$, so the class of $g$ is $r(\alpha)$. If $r_1(\alpha) = r_2(\alpha)$ with $\deg r_1, \deg r_2 < n$, then $f \mid r_1 - r_2$. A nonzero multiple of a monic polynomial of degree $n$ has degree at least $n$, so $r_1 = r_2$. The case of constant $r_j$ gives the injectivity of $R \to A$.

(4) In the principal ideal domain $k[X]$, an irreducible element generates a maximal ideal (Volume 6, Chapter 6). Part 3, applied to $f$ made monic, gives the basis $1, \alpha, \dots, \alpha^{n-1}$. $\square$

**Corollary (Existence of roots).** Let $k$ be a field and $f \in k[X]$ of positive degree. There is a field $L \supseteq k$ in which $f$ has a root, with $[L : k] \le \deg f$.

*Proof.* Let $q$ be an irreducible factor of $f$ and $L = k[X]/(q)$. The class of $X$ is a root of $q$, and so of $f$. $\square$

Induction on the degree gives a field in which $f$ splits into linear factors. Volume 11 treats these splitting fields.

::: mathlib
`AdjoinRoot` · `Mathlib.RingTheory.AdjoinRoot`

`AdjoinRoot f` is `Polynomial R ⧸ Ideal.span {f}`. The quotient map is `AdjoinRoot.mk f`, the root `AdjoinRoot.root f`, and `AdjoinRoot.of f : R →+* AdjoinRoot f` maps the coefficients. `mk_eq_zero` says `mk f g = 0 ↔ f ∣ g`, and `isRoot_root` is part 1. The instance `AdjoinRoot.instField` needs `[Fact (Irreducible f)]`, given by `haveI := Fact.mk hf`. `AdjoinRoot.powerBasis` is the basis of part 3, and `of.injective_of_degree_ne_zero` the injectivity.

<?decl AdjoinRoot?>
:::

::: mathlib
`AdjoinRoot.lift` · `Mathlib.RingTheory.AdjoinRoot`

`lift i x h : AdjoinRoot f →+* S` for `i : R →+* S` and `h : f.eval₂ i x = 0`. `lift_root` says that it sends the root to `x`. The algebra form is `liftAlgHom`, and `algHom_ext` gives the uniqueness of part 2.

<?decl AdjoinRoot.lift?>
:::

### Examples

**Example (A double root).** Let $f = X^3 - 3X + 2$. Then $f(1) = 0$ and $f' = 3X^2 - 3$ with $f'(1) = 0$. So $(X - 1)^2 \mid f$, and indeed $f = (X - 1)^2 (X + 2)$. As $f''(1) = 6 \ne 0$, the multiplicity of $1$ is exactly $2$.

**Example ($\mathbb{Q}[X]/(X^2 - 2)$).** The polynomial $X^2 - 2$ is irreducible over $\mathbb{Q}$ (Section 2), so $A = \mathbb{Q}[\alpha]$ with $\alpha^2 = 2$ is a field with basis $1, \alpha$. The universal property with $s = \sqrt 2$ embeds $A$ in $\mathbb{R}$. The inverse of $1 + \alpha$ comes from $(1 + \alpha)(\alpha - 1) = \alpha^2 - 1 = 1$, so $(1 + \alpha)^{-1} = \alpha - 1$.

**Counterexample (Reducible $f$ gives zero divisors).** Let $f = X^2 - 1 \in \mathbb{Q}[X]$. In $A = \mathbb{Q}[X]/(f)$, $(\alpha - 1)(\alpha + 1) = \alpha^2 - 1 = 0$, but $\alpha \pm 1 \ne 0$, since $f$ does not divide $X \pm 1$. So $A$ is not a domain. By the Chinese remainder theorem of Chapter 1, $A \cong \mathbb{Q} \times \mathbb{Q}$.

**Counterexample (Characteristic $p$).** Part 2 of the theorem on square factors fails in characteristic $p$. Let $k = \mathbb{F}_p(t)$ and $f = X^p - t \in k[X]$. Then $f' = p X^{p-1} = 0$, so $\gcd(f, f') = f \ne 1$. But $f$ is irreducible, hence squarefree: $f$ is monic and Eisenstein at the prime $t$ of the unique factorization domain $\mathbb{F}_p[t]$, so it is irreducible over $\mathbb{F}_p(t)$ by Section 2. Over $L = k[X]/(f)$ with root $\beta$, $f = (X - \beta)^p$.

### The library around it

The Wronskian $W(a, b) = a b' - a' b$ of two polynomials is `Polynomial.wronskian a b`, in `Mathlib.RingTheory.Polynomial.Wronskian`. It is bilinear and alternating (`Polynomial.wronskianBilin`, `Polynomial.isAlt_wronskianBilin`), its degree is less than the sum of the degrees, `Polynomial.degree_wronskian_lt_add`, and for coprime $a, b$ over a domain it vanishes exactly when both derivatives vanish, `IsCoprime.wronskian_eq_zero_iff`. The module `Mathlib.RingTheory.Polynomial.Radical` connects the Wronskian with multiple roots over a field: the quotient of $a$ by its radical divides $a'$, `divRadical_dvd_derivative`, and also $W(a, b)$, `divRadical_dvd_wronskian_left`. These facts are the core of the proof of the Mason and Stothers theorem. The module `Mathlib.RingTheory.Polynomial.SeparableDegree` treats the case $f' = 0$ in characteristic $p$: an irreducible $f$ has the form $g(X^{q^m})$ with $g$ separable, `Irreducible.hasSeparableContraction`, and the degree of $g$ is the separable degree `Polynomial.HasSeparableContraction.degree`, which divides the degree of $f$, `Polynomial.HasSeparableContraction.dvd_degree`. The module `Mathlib.RingTheory.Polynomial.Nilpotent` describes the units and the nilpotent elements of $R[X]$ for a commutative ring $R$: a polynomial is nilpotent exactly when all its coefficients are nilpotent, `Polynomial.isNilpotent_iff`, and it is a unit exactly when its constant term is a unit and its other coefficients are nilpotent, `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`. Over a reduced ring no polynomial of positive degree is a unit, `Polynomial.not_isUnit_of_degree_pos_of_isReduced`.

`Polynomial.isRoot_of_isRoot_of_dvd_derivative_mul` is a variant of the multiple root theorem. `Polynomial.Separable.squarefree` and, over a perfect field, `PerfectField.separable_iff_squarefree` link the two notions, with their home in Volume 11. `IsAdjoinRoot` is a predicate for rings presented as `AdjoinRoot f`. A common error of a learner: `AdjoinRoot.of f` is injective only under a hypothesis such as `f.degree ≠ 0` over a field, since for $f = 1$ the quotient is the zero ring.

### Exercises

1. (A) Compute the multiplicity of each root of $X^5 - 3X^4 + 3X^3 - X^2$ over $\mathbb{Q}$ by derivatives.
2. (A) Show that $X^n - 1$ has no multiple root in any field of characteristic $0$, and none in a field of characteristic $p$ with $p \nmid n$.
3. (A) In $\mathbb{Q}[X]/(X^3 - 2)$ with root $\alpha$, compute $(1 + \alpha)^{-1}$ in the basis $1, \alpha, \alpha^2$. Hint: $(1 + \alpha)(1 - \alpha + \alpha^2) = 1 + \alpha^3$.
4. (B) Show that $\mathbb{F}_2[X]/(X^3 + X + 1)$ is a field with $8$ elements and that its multiplicative group is cyclic of order $7$.
5. (B) Let $R$ be a commutative ring and $f \in R[X]$ monic of degree $n$. Show that $R[X]/(f)$ is a free $R$-module of rank $n$. Give an example where $f$ is not monic and $R \to R[X]/(f)$ is not injective. Hint: $f = 2X + 1$ over $\mathbb{Z}/4$ is a unit, since $(2X + 1)^2 = 1$.
6. (C) Let $k$ be a field of characteristic $p > 0$ and $f \in k[X]$ irreducible. Show that $\gcd(f, f') \ne 1$ if and only if $f = g(X^p)$ for some $g \in k[X]$. Hint: $f' = 0$ is the only way for $f \mid f'$.

### Notes and history

Kronecker built roots as classes of polynomials in the 1880s, so that no root had to be found inside $\mathbb{C}$.

### Reference

<?reference?>
