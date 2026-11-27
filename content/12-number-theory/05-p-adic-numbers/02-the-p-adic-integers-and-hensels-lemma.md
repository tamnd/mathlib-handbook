---
title: The p-adic integers and Hensel's lemma
kind: theory
modules:
  - Mathlib.NumberTheory.Padics.PadicIntegers
  - Mathlib.NumberTheory.Padics.Hensel
  - Mathlib.NumberTheory.Padics.RingHoms
explains:
  E3: [PadicInt, PadicInt.isUnit_iff, PadicInt.toZModPow, hensels_lemma]
  E2: [PadicInt.maximalIdeal_eq_span_p, PadicInt.ideal_eq_span_pow_p, PadicInt.instIsDiscreteValuationRing, PadicInt.norm_le_one, PadicInt.unitCoeff, PadicInt.unitCoeff_spec, PadicInt.exists_mem_range, PadicInt.toZMod, PadicInt.ker_toZMod, PadicInt.ker_toZModPow, PadicInt.zmod_cast_comp_toZModPow, PadicInt.lift, PadicInt.denseRange_natCast, PadicInt.residueField]
  E1: auto
families: [PadicInt.*]
requires: [V12.C01, V13.C03, V06.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The p-adic integers and Hensel's lemma

### Overview

The $p$-adic integers are the elements of $\mathbb{Q}_p$ of norm at most $1$. They form a subring $\mathbb{Z}_p$ with a simple ideal structure: the only nonzero ideals are the ideals $p^n\mathbb{Z}_p$, and the units are the elements of norm $1$. For each $n$ there is a ring homomorphism $\mathbb{Z}_p \to \mathbb{Z}/p^n\mathbb{Z}$, and an element of $\mathbb{Z}_p$ is the same as a compatible family of residues modulo $p, p^2, p^3, \dots$.

Hensel's lemma is the main tool to solve equations in $\mathbb{Z}_p$. It says that an approximate root of a polynomial, good enough compared to the derivative, is close to an exact root. The proof is Newton's method. Hensel's lemma turns a congruence modulo $p$ into a solution in $\mathbb{Z}_p$, and so into solutions modulo every power of $p$.

### Definitions

**Definition ($p$-adic integers).** $\mathbb{Z}_p = \{x \in \mathbb{Q}_p : |x|_p \le 1\}$.

Remarks. $\mathbb{Z}_p$ contains $0$ and $1$, and is closed under products by multiplicativity and under sums by the strong triangle inequality. So it is a subring. It is closed in $\mathbb{Q}_p$, so it is complete. The rationals in $\mathbb{Z}_p$ are the fractions $a/b$ with $p \nmid b$. The element $p$ has norm $p^{-1}$, so it lies in $\mathbb{Z}_p$ and is not a unit.

::: mathlib
`PadicInt` · `Mathlib.NumberTheory.Padics.PadicIntegers`

`PadicInt p`, with the notation `ℤ_[p]`, is the subtype `{x : ℚ_[p] // ‖x‖ ≤ 1}`. It carries its own ring, norm and metric instances. The bound `‖x‖ ≤ 1` is `PadicInt.norm_le_one`. The instance `PadicInt.isFractionRing` makes `ℚ_[p]` the field of fractions of `ℤ_[p]`.

<?decl PadicInt?>
:::

**Definition (Reduction modulo $p^n$).** For $n \ge 0$, the reduction map $\mathbb{Z}_p \to \mathbb{Z}/p^n\mathbb{Z}$ sends $x$ to the class of an integer $a$ with $|x - a|_p \le p^{-n}$. The theorem below shows that such an integer exists and that its class is well defined.

::: mathlib
`PadicInt.toZModPow` · `Mathlib.NumberTheory.Padics.RingHoms`

`PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)`, and `PadicInt.toZMod : ℤ_[p] →+* ZMod p` for $n = 1$. The kernels are `PadicInt.ker_toZModPow`, the ideal `Ideal.span {p ^ n}`, and `PadicInt.ker_toZMod`, the maximal ideal. The compatibility of the maps for $m \le n$ is `PadicInt.zmod_cast_comp_toZModPow`.

<?decl PadicInt.toZModPow?>
:::

### Theorems and proofs

**Theorem (Units and ideals of $\mathbb{Z}_p$).**

1. $x \in \mathbb{Z}_p$ is a unit if and only if $|x|_p = 1$.
2. Each $x \ne 0$ in $\mathbb{Z}_p$ is $x = p^n u$ with $n = v_p(x) \ge 0$ and $u$ a unit.
3. The nonzero ideals of $\mathbb{Z}_p$ are the ideals $p^n\mathbb{Z}_p$ with $n \ge 0$. So $\mathbb{Z}_p$ is a principal ideal domain with exactly one maximal ideal $p\mathbb{Z}_p$.

*Proof.* (1) If $xy = 1$ with $x, y \in \mathbb{Z}_p$, then $|x|_p|y|_p = 1$ and both are at most $1$, so $|x|_p = 1$. If $|x|_p = 1$, then $|x^{-1}|_p = 1$, so $x^{-1} \in \mathbb{Z}_p$.

(2) Let $n = v_p(x)$, so $|x|_p = p^{-n} \le 1$ and $n \ge 0$. Then $u = p^{-n}x$ has norm $1$, and it is a unit by (1).

(3) Let $I \ne 0$ be an ideal, and let $n$ be the least valuation of an element of $I$, taken at $x = p^nu$. Then $p^n = xu^{-1} \in I$, so $p^n\mathbb{Z}_p \subseteq I$. Each $y \in I$ has $v_p(y) \ge n$, so $y = p^n \cdot p^{v_p(y) - n}u'$ lies in $p^n\mathbb{Z}_p$. So $I = p^n\mathbb{Z}_p$. These ideals form the chain $\mathbb{Z}_p \supsetneq p\mathbb{Z}_p \supsetneq p^2\mathbb{Z}_p \supsetneq \cdots$, so the maximal ideal is $p\mathbb{Z}_p$. $\mathbb{Z}_p$ is a domain as a subring of a field. $\square$

A principal ideal domain with exactly one nonzero prime ideal is a discrete valuation ring, and $p$ is a uniformizer.

::: mathlib
`PadicInt.isUnit_iff` · `Mathlib.NumberTheory.Padics.PadicIntegers`

Statement (1): `IsUnit z ↔ ‖z‖ = 1`. Statement (2) is `PadicInt.unitCoeff_spec`: for `x ≠ 0`, `x = (PadicInt.unitCoeff hx : ℤ_[p]) * p ^ x.valuation`. Statement (3) is `PadicInt.ideal_eq_span_pow_p` and `PadicInt.maximalIdeal_eq_span_p`, and the instances `PadicInt.instIsLocalRing` and `PadicInt.instIsDiscreteValuationRing` record the structure.

<?decl PadicInt.isUnit_iff?>
:::

**Theorem (Approximation by integers).** For $x \in \mathbb{Z}_p$ and $n \ge 0$ there is a unique integer $a$ with $0 \le a < p^n$ and $|x - a|_p \le p^{-n}$. The map $x \mapsto a \bmod p^n$ is a surjective ring homomorphism $\mathbb{Z}_p \to \mathbb{Z}/p^n\mathbb{Z}$ with kernel $p^n\mathbb{Z}_p$.

*Proof.* Existence. Since $\mathbb{Q}$ is dense in $\mathbb{Q}_p$, there is $r \in \mathbb{Q}$ with $|x - r|_p \le p^{-n}$. Then $|r|_p \le \max(|x|_p, |x - r|_p) \le 1$, so $r = c/b$ with $p \nmid b$. Choose an integer $b'$ with $bb' \equiv 1 \pmod{p^n}$ (Volume 2, Chapter 3), and let $a$ be the residue of $cb'$ in $[0, p^n)$. Then
$$r - a = \frac{c - ab}{b}, \qquad c - ab \equiv c - cb'b \equiv 0 \pmod {p^n},$$
so $|r - a|_p \le p^{-n}$, and $|x - a|_p \le \max(|x - r|_p, |r - a|_p) \le p^{-n}$.

Uniqueness. If $a$ and $a'$ both work, then $|a - a'|_p \le p^{-n}$, so $p^n \mid a - a'$, and $a = a'$ since both lie in $[0, p^n)$.

Homomorphism. If $|x - a|_p, |y - b|_p \le p^{-n}$, then $|(x + y) - (a + b)|_p \le p^{-n}$, and
$$xy - ab = x(y - b) + b(x - a)$$
has norm at most $p^{-n}$ since $|x|_p, |b|_p \le 1$. So the class of $x + y$ is that of $a + b$, and the class of $xy$ is that of $ab$. The map sends the integer $a$ to its class, so it is surjective. Its kernel is the set of $x$ with $|x|_p \le p^{-n}$, which is $p^n\mathbb{Z}_p$. $\square$

The reductions are compatible: reducing modulo $p^n$ and then modulo $p^m$ for $m \le n$ gives the reduction modulo $p^m$. Conversely, a compatible family of classes $a_n \bmod p^n$ defines an element of $\mathbb{Z}_p$: the integers $a_n$ form a Cauchy sequence, since $|a_{n+1} - a_n|_p \le p^{-n}$. So $\mathbb{Z}_p$ is the inverse limit of the rings $\mathbb{Z}/p^n\mathbb{Z}$. In particular each $x \in \mathbb{Z}_p$ has a unique expansion $x = \sum_{k\ge0} c_k p^k$ with digits $0 \le c_k < p$.

::: mathlib
`PadicInt.lift` · `Mathlib.NumberTheory.Padics.RingHoms`

The universal property of the inverse limit: a compatible family `f k : R →+* ZMod (p ^ k)` gives `R →+* ℤ_[p]`. The case $n = 1$ of the theorem is `PadicInt.exists_mem_range`: `∃ n < p, x - n ∈ maximalIdeal ℤ_[p]`. Density of `ℕ` in `ℤ_[p]` is `PadicInt.denseRange_natCast`, and `PadicInt.residueField` identifies the residue field with `ZMod p`.

<?decl PadicInt.lift?>
:::

**Lemma (Taylor expansion).** Let $F \in \mathbb{Z}_p[X]$. There are polynomials $G, H \in \mathbb{Z}_p[X, Y]$ with
$$F(x + h) = F(x) + F'(x)h + h^2G(x, h), \qquad F'(x + h) = F'(x) + hH(x, h).$$

*Proof.* By linearity it is enough to treat $F = X^m$. The binomial theorem gives $(x + h)^m = x^m + mx^{m-1}h + h^2\sum_{i\ge2}\binom mi x^{m-i}h^{i-2}$, and the binomial coefficients are integers. The second identity is the identity $F'(x + h) - F'(x) = h \cdot (\ldots)$, true for every polynomial since $X - Y$ divides $X^k - Y^k$. $\square$

Since the coefficients of $G$ and $H$ lie in $\mathbb{Z}_p$, $|G(x, h)|_p \le 1$ and $|H(x, h)|_p \le 1$ for $x, h \in \mathbb{Z}_p$.

**Theorem (Hensel's lemma).** Let $F \in \mathbb{Z}_p[X]$ and $a \in \mathbb{Z}_p$ with $|F(a)|_p < |F'(a)|_p^2$. Then there is a unique $z \in \mathbb{Z}_p$ with $F(z) = 0$ and $|z - a|_p < |F'(a)|_p$, and this root has $|F'(z)|_p = |F'(a)|_p$.

*Proof.* Put $c = |F'(a)|_p > 0$ and $t = |F(a)|_p/c^2 < 1$. Define Newton's sequence $a_0 = a$ and
$$a_{n+1} = a_n - \frac{F(a_n)}{F'(a_n)}.$$

Claim: for each $n$, $a_n \in \mathbb{Z}_p$, $|F'(a_n)|_p = c$, $|F(a_n)|_p \le c^2t^{2^n}$, and $|a_n - a|_p \le ct$.

The claim holds for $n = 0$. Assume it for $n$, and let $h = -F(a_n)/F'(a_n)$. Then
$$|h|_p = \frac{|F(a_n)|_p}{c} \le ct^{2^n} \le ct < c \le 1,$$
so $h \in \mathbb{Z}_p$ and $a_{n+1} = a_n + h \in \mathbb{Z}_p$. By the Taylor expansion, $F(a_n + h) = F(a_n) + F'(a_n)h + h^2G = h^2G$, so
$$|F(a_{n+1})|_p \le |h|_p^2 \le c^2t^{2^{n+1}}.$$
Also $F'(a_{n+1}) = F'(a_n) + hH$ with $|hH|_p \le |h|_p < c = |F'(a_n)|_p$, so $|F'(a_{n+1})|_p = c$ by property (3) of Section 1. Finally $|a_{n+1} - a|_p \le \max(|a_n - a|_p, |h|_p) \le ct$. This proves the claim.

Existence. $|a_{n+1} - a_n|_p \le ct^{2^n} \to 0$, so $(a_n)$ is Cauchy by the strong triangle inequality, and it has a limit $z \in \mathbb{Z}_p$ since $\mathbb{Z}_p$ is complete. Polynomials are continuous, so $F(z) = \lim F(a_n) = 0$, since $|F(a_n)|_p \to 0$. The set $\{x : |x - a|_p \le ct\}$ is closed, so $|z - a|_p \le ct < c$. The norm $|F'(a_n)|_p$ is constant equal to $c$, and $F'(a_n) \to F'(z)$, so $|F'(z)|_p = c$.

Uniqueness. Let $z'$ be a root with $|z' - a|_p < c$, and $h = z' - z$. Then $|h|_p \le \max(|z' - a|_p, |a - z|_p) < c$. The Taylor expansion at $z$ gives $0 = F(z + h) = h(F'(z) + hG)$. If $h \ne 0$, then $F'(z) = -hG$ and $c = |F'(z)|_p \le |h|_p < c$, which is false. So $z' = z$. $\square$

The case used most is $|F'(a)|_p = 1$: if $F(a) \equiv 0 \pmod p$ and $F'(a) \not\equiv 0 \pmod p$, then $F$ has a unique root $z \equiv a \pmod p$ in $\mathbb{Z}_p$.

::: mathlib
`hensels_lemma` · `Mathlib.NumberTheory.Padics.Hensel`

The statement takes `F : R[X]` with `[Algebra R ℤ_[p]]`, evaluated with `Polynomial.aeval`, so it applies directly to polynomials over `ℤ`. The hypothesis is `‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2`, and the conclusion has the four parts of the theorem.

<?decl hensels_lemma?>
:::

### Examples

**Example (A square root of $2$ in $\mathbb{Z}_7$).** Let $F = X^2 - 2$ and $a = 3$. Then $F(3) = 7$, so $|F(3)|_7 = \frac17$, and $F'(3) = 6$ has norm $1$. Hensel's lemma gives a unique $z \in \mathbb{Z}_7$ with $z^2 = 2$ and $z \equiv 3 \pmod 7$. Newton's method gives the digits: $a_1 = 3 - \frac{7}{6}$, and modulo $49$, $6^{-1} \equiv 41$ since $6 \cdot 41 = 246 = 5 \cdot 49 + 1$, so $a_1 \equiv 3 - 7 \cdot 41 = -284 \equiv 10 \pmod{49}$. Check: $10^2 = 100 = 2 \cdot 49 + 2$. So $z = 3 + 1 \cdot 7 + \cdots$. The other root is $-z \equiv 4 \pmod 7$.

**Example (The strong form at $p = 2$).** Let $F = X^2 + 7$ and $a = 1$. Then $F(1) = 8$ has $|8|_2 = \frac18$ and $F'(1) = 2$ has $|2|_2^2 = \frac14$. Since $\frac18 < \frac14$, there is $z \in \mathbb{Z}_2$ with $z^2 = -7$ and $|z - 1|_2 < \frac12$. The simple form with $|F'(a)|_p = 1$ never applies to $X^2 - c$ at $p = 2$, since $F' = 2X$. The same argument shows that $1 - p$ is a square in $\mathbb{Z}_p$ for $p$ odd: take $F = X^2 - (1 - p)$ and $a = 1$, with $|F(1)|_p = \frac1p$ and $|F'(1)|_p = |2|_p = 1$.

**Counterexample (A root modulo $p$ that does not lift).** Take $F = X^2 - 3$ at $p = 3$ and $a = 0$: $F(0) = -3 \equiv 0 \pmod 3$, but $F'(0) = 0$. There is no root in $\mathbb{Z}_3$: a root $z$ has $2v_3(z) = v_3(3) = 1$, which is impossible. So the hypothesis on the derivative cannot be dropped.

**Counterexample ($\mathbb{Z}_p$ is not $\mathbb{Z}$).** $\frac12 \in \mathbb{Z}_3$ since $|2|_3 = 1$, and its digit expansion is $\frac12 = 2 + 1\cdot 3 + 1\cdot 3^2 + \cdots$, as $2 + 3 \cdot \frac{1}{1 - 3} = 2 - \frac32 = \frac12$. The ring $\mathbb{Z}_p$ is uncountable, since the digit sequences are arbitrary.

### The library around it

The file `Mathlib.NumberTheory.Padics.RingHoms` gives the reductions, the approximations `PadicInt.appr` and `PadicInt.zmodRepr`, and `PadicInt.lift`. The file `Mathlib.NumberTheory.Padics.Hensel` proves `hensels_lemma` with Newton's method. Other files of the folder treat Mahler's theorem on continuous functions $\mathbb{Z}_p \to \mathbb{Q}_p$.

Common errors of a learner:

- An element of `ℤ_[p]` is a pair of an element of `ℚ_[p]` and a proof. To build one, give the proof: `⟨x, hx⟩` with `hx : ‖x‖ ≤ 1`.
- `hensels_lemma` uses the real norm `‖·‖`, not `padicNormE`. Bounds such as `‖(7 : ℤ_[7])‖ = 7⁻¹` come from `PadicInt.norm_p`.

### Exercises

1. (A) Find the first three $5$-adic digits of the two square roots of $-1$ in $\mathbb{Z}_5$.
2. (A) Find the $3$-adic expansion of $-\frac{1}{2}$ and of $\frac14$.
3. (A) Show that $\sqrt 2 \notin \mathbb{Q}_5$ and $\sqrt 5 \notin \mathbb{Q}_5$.
4. (B) Show that the polynomial $X^{p-1} - 1$ has $p - 1$ distinct roots in $\mathbb{Z}_p$, one in each nonzero class modulo $p$. These are the Teichmüller representatives.
5. (B) Let $p$ be odd and $u \in \mathbb{Z}_p$ a unit. Show that $u$ is a square in $\mathbb{Z}_p$ if and only if its reduction is a square in $\mathbb{Z}/p\mathbb{Z}$. Deduce that $\mathbb{Q}_p^\times/(\mathbb{Q}_p^\times)^2$ has $4$ elements.
6. (B) Show that a unit $u \in \mathbb{Z}_2$ is a square if and only if $u \equiv 1 \pmod 8$.
7. (C) Show that a polynomial $F \in \mathbb{Z}[X]$ has a root in $\mathbb{Z}_p$ if and only if the congruence $F(x) \equiv 0 \pmod{p^n}$ has a solution for every $n$. Hint: for the converse, use the compactness of $\mathbb{Z}_p$, or choose the solutions in a compatible way with König's lemma.

### Notes and history

Hensel stated and used the lemma that bears his name in his work on $p$-adic numbers around the turn of the twentieth century. A reference is Gouvêa, *p-adic Numbers: An Introduction*, Chapter 3, and Serre, *A Course in Arithmetic*, Chapter II.

### Reference

<?reference?>
