---
title: Multiplicative and Dirichlet characters
kind: theory
modules:
  - Mathlib.NumberTheory.MulChar.Basic
  - Mathlib.NumberTheory.MulChar.Duality
  - Mathlib.NumberTheory.DirichletCharacter.Basic
  - Mathlib.NumberTheory.DirichletCharacter.Orthogonality
  - Mathlib.NumberTheory.GaussSum
  - Mathlib.NumberTheory.LegendreSymbol.AddCharacter
  - Mathlib.NumberTheory.AddCharacter.Trace
  - Mathlib.NumberTheory.LegendreSymbol.Complex
  - Mathlib.NumberTheory.JacobiSum.Basic
  - Mathlib.NumberTheory.DirichletCharacter.GaussSum
  - Mathlib.NumberTheory.DirichletCharacter.Bounds
  - Mathlib.NumberTheory.MulChar.Lemmas
explains:
  E3: [MulChar, DirichletCharacter, DirichletCharacter.sum_characters_eq, DirichletCharacter.sum_char_inv_mul_char_eq]
  E2: [MulChar.equivToUnitHom, MulChar.toUnitHom, MulChar.ofUnitHom, MulChar.IsQuadratic, MulChar.sum_eq_zero_of_ne_one, MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity, MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, DirichletCharacter.sum_characters_eq_zero, DirichletCharacter.Even, DirichletCharacter.Odd, DirichletCharacter.changeLevel, DirichletCharacter.conductor, DirichletCharacter.IsPrimitive, DirichletCharacter.primitiveCharacter, gaussSum, gaussSum_mul_gaussSum_eq_card, gaussSum_sq]
  E1: auto
families: [MulChar.*, DirichletCharacter.*, gaussSum_*]
requires: [V12.C03, V05.C03, V05.C04, V06.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Multiplicative and Dirichlet characters

### Overview

A Dirichlet character modulo $n$ is a function $\chi : \mathbb{Z} \to \mathbb{C}$ that is periodic modulo $n$, multiplicative, and zero on the integers not prime to $n$. The Legendre symbol $\left(\frac{\cdot}{p}\right)$ of Chapter 3 is one. Characters are the tool that isolates an arithmetic progression: the orthogonality relations give
$$\frac{1}{\varphi(n)}\sum_{\chi}\overline{\chi(a)}\chi(m) = \begin{cases}1 & m \equiv a \pmod n,\\ 0 & \text{otherwise,}\end{cases}$$
for $a$ prime to $n$. Dirichlet used this identity in 1837 to prove that each progression $a, a + n, a + 2n, \dots$ with $\gcd(a, n) = 1$ contains infinitely many primes (Chapter 7).

### Definitions

**Definition (Multiplicative character).** Let $M$ be a commutative monoid and $R$ a commutative ring. A multiplicative character $\chi : M \to R$ is a map with $\chi(1) = 1$, $\chi(ab) = \chi(a)\chi(b)$, and $\chi(a) = 0$ for each $a$ that is not a unit of $M$. The characters form a commutative group under pointwise product on the units; the trivial character $1$ is $1$ on units and $0$ elsewhere. A character is quadratic if its values lie in $\{0, 1, -1\}$.

Remarks. A character is fixed by its values on the units $M^\times$, and these values are units of $R$. Conversely each group homomorphism $M^\times \to R^\times$, extended by $0$, is a character. So the characters of $M$ are the homomorphisms $M^\times \to R^\times$.

::: mathlib
`MulChar` · `Mathlib.NumberTheory.MulChar.Basic`

`MulChar R R'` is a structure that extends `MonoidHom R R'` with the field `map_nonunit'`. The equivalence with unit homomorphisms is `MulChar.equivToUnitHom : MulChar R R' ≃ (Rˣ →* R'ˣ)`. Quadratic characters satisfy `MulChar.IsQuadratic`.

<?decl MulChar?>
:::

**Definition (Dirichlet character).** A Dirichlet character of level $n$ with values in $R$ is a multiplicative character $\mathbb{Z}/n\mathbb{Z} \to R$. It defines the function $m \mapsto \chi(m \bmod n)$ on $\mathbb{Z}$. It is even if $\chi(-1) = 1$ and odd if $\chi(-1) = -1$.

::: mathlib
`DirichletCharacter` · `Mathlib.NumberTheory.DirichletCharacter.Basic`

`DirichletCharacter R n` is the abbreviation `MulChar (ZMod n) R`. The predicates are `DirichletCharacter.Even` and `DirichletCharacter.Odd`. The lemma `DirichletCharacter.apply_eq_zero_iff` says `χ a = 0 ↔ ¬IsCoprime a n` for `a : ℤ`.

<?decl DirichletCharacter?>
:::

**Definition (Level change, conductor).** If $n \mid m$, a character $\chi$ of level $n$ gives a character of level $m$, by composing with the map $(\mathbb{Z}/m)^\times \to (\mathbb{Z}/n)^\times$. A character $\chi$ of level $n$ factors through $d \mid n$ if it comes in this way from a character of level $d$. The conductor of $\chi$ is the least such $d$, and $\chi$ is primitive if its conductor is $n$.

Remarks. The character of level $m$ obtained from $\chi$ agrees with $\chi$ on the integers prime to $m$, and is $0$ on the others. The conductor divides every $d$ through which $\chi$ factors, and the primitive character of conductor $d$ that induces $\chi$ is unique.

::: mathlib
`DirichletCharacter.changeLevel` · `Mathlib.NumberTheory.DirichletCharacter.Basic`

`changeLevel (h : n ∣ m) : DirichletCharacter R n →* DirichletCharacter R m`. The predicate `FactorsThrough χ d`, the number `DirichletCharacter.conductor χ` and the predicate `DirichletCharacter.IsPrimitive` follow the definition.

<?decl DirichletCharacter.changeLevel?>
:::

### Theorems and proofs

Let $G$ be a finite abelian group, written multiplicatively, and $\widehat G$ the group of homomorphisms $G \to \mathbb{C}^\times$. Each value $\chi(g)$ is a root of unity, since $g^{|G|} = 1$.

**Lemma (Extension).** Let $H \le G$, $g \in G$, $K = \langle H, g\rangle$, and let $m \ge 1$ be least with $g^m \in H$. Each $\chi \in \widehat H$ has exactly $m$ extensions to $K$, and $|K| = m|H|$.

*Proof.* Each element of $K$ has the form $hg^i$ with $h \in H$ and $0 \le i < m$, and this form is unique: if $hg^i = h'g^j$ with $0 \le i \le j < m$, then $g^{j - i} \in H$, so $j = i$ by the minimality of $m$, and $h = h'$. So $|K| = m|H|$.

An extension $\psi$ is fixed by $w = \psi(g)$, which satisfies $w^m = \chi(g^m)$. The number $\chi(g^m) \ne 0$ has exactly $m$ complex $m$-th roots. Conversely, for such a $w$ put $\psi(hg^i) = \chi(h)w^i$. For a product, $hg^i \cdot h'g^j = hh'g^{i+j}$; if $i + j \ge m$, the normal form is $(hh'g^m)g^{i + j - m}$, and
$$\psi = \chi(hh')\chi(g^m)w^{i + j - m} = \chi(hh')w^{i+j} = \psi(hg^i)\psi(h'g^j).$$
The case $i + j < m$ is direct. So $\psi$ is a homomorphism. $\square$

**Theorem (Number of characters and separation).** $|\widehat G| = |G|$, and for each $g \ne 1$ in $G$ there is $\chi \in \widehat G$ with $\chi(g) \ne 1$.

*Proof.* Build a chain $\{1\} = H_0 < H_1 < \cdots < H_k = G$ with $H_{j+1} = \langle H_j, g_j\rangle$. By the lemma, each character of $H_j$ has $[H_{j+1} : H_j]$ extensions, so the number of characters of $H_{j+1}$ is $[H_{j+1} : H_j] \cdot |\widehat{H_j}|$. By induction $|\widehat G| = |G|$.

For $g \ne 1$ of order $m > 1$, start the chain with $H_1 = \langle g\rangle$, and take the character $\chi(g^i) = e^{2\pi i\, i/m}$ of $H_1$, the extension of the trivial character with $w = e^{2\pi i/m} \ne 1$. Extend it step by step to $G$ by the lemma. $\square$

**Theorem (Orthogonality).** Let $G$ be a finite abelian group.

1. For $\chi \ne 1$, $\sum_{g \in G}\chi(g) = 0$.
2. For $g \ne 1$, $\sum_{\chi \in \widehat G}\chi(g) = 0$.
3. For $g, h \in G$, $\sum_{\chi}\chi(g)^{-1}\chi(h) = |G|$ if $g = h$ and $0$ otherwise.

*Proof.* (1) Choose $h$ with $\chi(h) \ne 1$. Since $g \mapsto hg$ is a bijection of $G$, $S = \sum_g\chi(hg) = \chi(h)S$, so $S = 0$.

(2) By the separation theorem choose $\psi$ with $\psi(g) \ne 1$. Since $\chi \mapsto \psi\chi$ is a bijection of $\widehat G$, $T = \sum_\chi\psi(g)\chi(g) = \psi(g)T$, so $T = 0$.

(3) $\chi(g)^{-1}\chi(h) = \chi(g^{-1}h)$. Apply (2) to $g^{-1}h$ if $g \ne h$; if $g = h$, each term is $1$ and there are $|G|$ terms. $\square$

For Dirichlet characters, $G = (\mathbb{Z}/n)^\times$ has $\varphi(n)$ elements. For $a$ prime to $n$ and any $m$,
$$\sum_{\chi \bmod n}\overline{\chi(a)}\chi(m) = \begin{cases}\varphi(n) & m \equiv a \pmod n,\\ 0 & \text{otherwise},\end{cases}$$
since $\chi(a)^{-1} = \overline{\chi(a)}$ for a root of unity, and both sides are $0$ for $m$ not prime to $n$.

::: mathlib
`DirichletCharacter.sum_char_inv_mul_char_eq` · `Mathlib.NumberTheory.DirichletCharacter.Orthogonality`

The statement of (3): for `IsUnit a`, `∑ χ, χ a⁻¹ * χ b = if a = b then n.totient else 0`. The relation (2) is `DirichletCharacter.sum_characters_eq_zero` and `DirichletCharacter.sum_characters_eq`. They hold for values in any domain `R` with `HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)`, which `ℂ` satisfies. The relation (1) holds for any finite monoid, `MulChar.sum_eq_zero_of_ne_one`.

<?decl DirichletCharacter.sum_char_inv_mul_char_eq?>
:::

::: mathlib
`DirichletCharacter.sum_characters_eq` · `Mathlib.NumberTheory.DirichletCharacter.Orthogonality`

`∑ χ, χ a = if a = 1 then n.totient else 0`. The count of characters is `DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity`, an instance of `MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity`, and the separation is `MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity`. Mathlib proves the count through the duality of finite abelian groups in `Mathlib.NumberTheory.MulChar.Duality`, not by the extension lemma.

<?decl DirichletCharacter.sum_characters_eq?>
:::

**Theorem (Gauss sums).** Let $p$ be a prime, $\zeta = e^{2\pi i/p}$, and for a character $\chi$ modulo $p$ let $\tau(\chi) = \sum_{a \in \mathbb{F}_p}\chi(a)\zeta^a$. If $\chi \ne 1$, then $\tau(\chi)\tau(\overline\chi) = \chi(-1)p$, and so $|\tau(\chi)|^2 = p$.

*Proof.* First, for $b \in \mathbb{F}_p$, $\sum_{c \in \mathbb{F}_p}\zeta^{bc}$ is $p$ if $b = 0$ and $0$ otherwise, as a geometric sum of the $p$-th roots of unity. Now
$$\tau(\chi)\tau(\overline\chi) = \sum_{a, b \ne 0}\chi(a)\overline\chi(b)\zeta^{a + b}.$$
For fixed $a \ne 0$, substitute $b = ac$ with $c \ne 0$. Since $\overline\chi(a) = \chi(a)^{-1}$, $\chi(a)\overline\chi(ac) = \overline\chi(c)$, and the sum becomes
$$\sum_{c \ne 0}\overline\chi(c)\sum_{a \ne 0}\zeta^{a(1 + c)}.$$
The inner sum is $p - 1$ for $c = -1$ and $-1$ otherwise. So the product is $(p - 1)\overline\chi(-1) - \sum_{c \ne 0, -1}\overline\chi(c) = p\,\overline\chi(-1) - \sum_{c \ne 0}\overline\chi(c) = p\,\chi(-1)$, by (1) and $\chi(-1) = \pm1$. Finally $\overline{\tau(\chi)} = \sum\overline\chi(a)\zeta^{-a} = \overline\chi(-1)\tau(\overline\chi)$, so $|\tau(\chi)|^2 = \chi(-1)\tau(\overline\chi)\tau(\chi) = p$. $\square$

For the Legendre symbol, $\overline\chi = \chi$, so $\tau(\chi)^2 = \left(\frac{-1}{p}\right)p$. This identity gives a proof of quadratic reciprocity different from that of Chapter 3.

::: mathlib
`gaussSum` · `Mathlib.NumberTheory.GaussSum`

`gaussSum χ ψ = ∑ a, χ a * ψ a` for a multiplicative character `χ : MulChar R R'` and an additive character `ψ : AddChar R R'` of a finite ring `R`. The theorem is `gaussSum_mul_gaussSum_eq_card` for a primitive `ψ` on a finite field: `gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = Fintype.card R`. The quadratic case is `gaussSum_sq`. The values may lie in any ring with the needed roots of unity, also of positive characteristic, which is how Mathlib uses Gauss sums to compute `χ 2` and quadratic reciprocity in `Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum`.

<?decl gaussSum?>
:::

### Examples

**Example (Characters modulo $5$).** $(\mathbb{Z}/5)^\times$ is cyclic with generator $2$: $2^0, 2^1, 2^2, 2^3 = 1, 2, 4, 3$. A character is fixed by $\chi(2) \in \{1, i, -1, -i\}$, so there are $4 = \varphi(5)$ characters:

| $a$ | 1 | 2 | 3 | 4 |
|---|---|---|---|---|
| $\chi_0$ | 1 | 1 | 1 | 1 |
| $\chi_1$ | 1 | $i$ | $-i$ | $-1$ |
| $\chi_2$ | 1 | $-1$ | $-1$ | 1 |
| $\chi_3$ | 1 | $-i$ | $i$ | $-1$ |

The character $\chi_2$ is the Legendre symbol modulo $5$. Each row other than $\chi_0$ sums to $0$, and each column other than $a = 1$ sums to $0$. The characters $\chi_1$ and $\chi_3$ are odd, and $\chi_0, \chi_2$ are even.

**Example (A character that is not primitive).** Modulo $4$ there are two characters: $\chi_0$ and $\chi_{-4}$ with $\chi_{-4}(1) = 1$, $\chi_{-4}(3) = -1$. Lift $\chi_{-4}$ to level $12$: it is $1$ on $1, 5$ and $-1$ on $7, 11$, and $0$ elsewhere. This character of level $12$ has conductor $4$, so it is not primitive. Its value at $3$ is $0$ although $\chi_{-4}(3) = -1$.

**Counterexample (Values in a ring without roots of unity).** With values in $\mathbb{Q}$, the only characters modulo $5$ are $\chi_0$ and $\chi_2$, since a value of $\chi(2)$ must satisfy $w^4 = 1$. The count $\varphi(n)$ and the orthogonality (2) fail: $\chi_0(4) + \chi_2(4) = 2 \ne 0$. This is why Mathlib assumes `HasEnoughRootsOfUnity`.

### The library around it

Mathlib separates three levels. `MulChar` is the general notion for any commutative monoid, with the duality theory of `Mathlib.NumberTheory.MulChar.Duality`. `DirichletCharacter R n` is the special case on `ZMod n`, with the conductor and the primitive characters in `Mathlib.NumberTheory.DirichletCharacter.Basic`. The Legendre and Jacobi symbols of Chapter 3 are built from the quadratic character `quadraticChar` of a finite field and the characters `ZMod.χ₄` and `ZMod.χ₈`, which are `MulChar` values. Gauss sums are in `Mathlib.NumberTheory.GaussSum`.

The additive characters that enter a Gauss sum are in `Mathlib.NumberTheory.LegendreSymbol.AddCharacter`. An additive character `ψ : AddChar R R'` is *primitive*, `AddChar.IsPrimitive`, if each shift $x \mapsto \psi(ax)$ with $a \neq 0$ is nontrivial. On a field each nontrivial character is primitive, by `AddChar.IsPrimitive.of_ne_one`. The orthogonality relations are `AddChar.sum_eq_zero_of_ne_one` and `AddChar.sum_mulShift`: for primitive $\psi$, $\sum_x \psi(xb)$ is $\lvert R \rvert$ for $b = 0$ and $0$ otherwise. On `ZMod n`, a root of unity $\zeta$ with $\zeta^n = 1$ gives `AddChar.zmodChar n`, with $a \mapsto \zeta^a$, and it is primitive when $\zeta$ is a primitive root, by `AddChar.zmodChar_primitive_of_primitive_root`. For a finite field $F$ and a field $F'$ of a different characteristic, `AddChar.FiniteField.primitiveChar F F'` is a primitive character with values in a cyclotomic extension of $F'$, of the type `AddChar.PrimitiveAddChar`. The module `Mathlib.NumberTheory.LegendreSymbol.Complex` gives the complex version `AddChar.FiniteField.primitiveChar_to_Complex`, with `AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive`. The module `Mathlib.NumberTheory.AddCharacter.Trace` builds characters of an algebra $A$ over `ZMod n` from the trace: `AddChar.traceChar A hζ` is $x \mapsto \zeta^{\operatorname{Tr}(x)}$, by `AddChar.traceChar_apply`, and on a finite field of characteristic $p$ it is primitive, by `AddChar.isPrimitive_traceChar`.

For Dirichlet characters, `Mathlib.NumberTheory.DirichletCharacter.GaussSum` relates Gauss sums and the conductor. If $\chi$ is primitive, then `gaussSum_mulShift_of_isPrimitive` says $g(\chi, \psi_a) = \bar\chi(a)g(\chi, \psi)$ for the shifted character $\psi_a(x) = \psi(ax)$, and `gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive` says that $g(\chi, \psi) = 0$ when $\psi$ is not primitive. Conversely, a nonzero Gauss sum for a character $\psi$ that is trivial on multiples of $d \mid N$ forces $\chi$ to factor through level $d$, by `factorsThrough_of_gaussSum_ne_zero`. The module `Mathlib.NumberTheory.DirichletCharacter.Bounds` proves that the values of a Dirichlet character with values in a normed field have norm at most $1$, `DirichletCharacter.norm_le_one`, and norm exactly $1$ at the units, `DirichletCharacter.unit_norm_eq_one`.

The Jacobi sum of two multiplicative characters of a finite ring is `jacobiSum χ φ` $= \sum_x \chi(x)\varphi(1 - x)$, in `Mathlib.NumberTheory.JacobiSum.Basic`. It is symmetric, `jacobiSum_comm`, and its special values are `jacobiSum_one_one`, equal to $q - 2$ for a field with $q$ elements, `jacobiSum_one_nontrivial`, equal to $-1$, and `jacobiSum_nontrivial_inv`, equal to $-\chi(-1)$. The main identity links it to Gauss sums: if $\chi\varphi \neq 1$ and $\psi$ is primitive, then $J(\chi, \varphi)g(\chi\varphi, \psi) = g(\chi, \psi)g(\varphi, \psi)$. This is `jacobiSum_mul_nontrivial`, with the quotient form `jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum`. The library also proves `jacobiSum_mul_jacobiSum_inv`, $J(\chi, \varphi)J(\chi^{-1}, \varphi^{-1}) = q$ for nontrivial $\chi$, $\varphi$ and $\chi\varphi$. An induction gives `gaussSum_pow_eq_prod_jacobiSum`, which writes $g(\chi, \psi)^m$ for the order $m$ of $\chi$ as $\chi(-1)\,q$ times a product of Jacobi sums. When the characters have order dividing $n$, the Jacobi sum lies in the ring generated by an $n$-th root of unity, `jacobiSum_mem_algebraAdjoin_of_pow_eq_one`, and `exists_jacobiSum_eq_neg_one_add` gives its congruence to $-1$ modulo $(\mu - 1)^2$.

The module `Mathlib.NumberTheory.MulChar.Lemmas` collects facts on the values and the orders of characters. On a finite cyclic monoid $M$, a generator $g$ and a root of unity $\zeta$ of order dividing $\lvert M^\times \rvert$ give the character `MulChar.ofRootOfUnity` with $g \mapsto \zeta$, by `MulChar.ofRootOfUnity_spec`, and `MulChar.equiv_rootsOfUnity` makes this a bijection between characters and roots of unity. For a finite field $F$, `MulChar.orderOf_dvd_card_sub_one` says that the order of a character divides $\lvert F \rvert - 1$, and `MulChar.exists_mulChar_orderOf` gives a character of each order $n \mid \lvert F \rvert - 1$ when the target has a primitive $n$-th root of unity. The values lie in roots of unity: `MulChar.apply_mem_rootsOfUnity_orderOf` for a nonzero $a$, and `MulChar.apply_mem_algebraAdjoin` says that $\chi(a)$ lies in $\mathbb{Z}[\mu]$ for a primitive root $\mu$ of order `orderOf χ`. The module also puts a star operation on characters with values in a star ring: `MulChar.starComp` composes with conjugation, and for complex values `MulChar.star_eq_inv` says that $\bar\chi = \chi^{-1}$ when the group of units is finite.

Common errors of a learner:

- `χ 0 = 0` holds only for level $n \ne 1$. Modulo $1$ every element is a unit, so the trivial character has `χ 0 = 1` (`DirichletCharacter.map_zero'` needs `n ≠ 1`).
- The sum `∑ χ, …` runs over the `Fintype` instance of `DirichletCharacter R n`, which exists for a domain `R`.

### Exercises

1. (A) Write the table of the characters modulo $8$, and check the orthogonality relations. Show that none of them takes the value $i$.
2. (A) Find all characters modulo $7$, and identify the Legendre symbol among them.
3. (A) Show that the number of even characters modulo $n > 2$ is $\varphi(n)/2$.
4. (B) Show that a nontrivial character modulo a prime $p$ is primitive, and find the conductor of each character modulo $9$.
5. (B) Let $\chi$ be a character modulo $n$ and $N \ge 1$. Show that $\left|\sum_{m=1}^{N}\chi(m)\right| \le \varphi(n)$ for $\chi \ne \chi_0$.
6. (B) Compute $\tau(\chi)$ for the Legendre symbol modulo $3$ and modulo $5$, and check $\tau^2 = \pm p$.
7. (C) Let $\chi$ be the Legendre symbol modulo an odd prime $p$ and $\tau = \tau(\chi)$. For an odd prime $q \ne p$, show that $\tau^q \equiv \chi(q)\tau \pmod q$ in $\mathbb{Z}[\zeta]$, and deduce the law of quadratic reciprocity from $\tau^2 = \chi(-1)p$.

### Notes and history

Dirichlet introduced the characters modulo $n$ in his 1837 proof of the theorem on primes in arithmetic progressions. Gauss used the sums that bear his name in his work on cyclotomy and determined the sign of the quadratic Gauss sum. The extension lemma above is the usual elementary route to the duality of finite abelian groups; another route goes through the structure theorem. A reference is Ireland and Rosen, *A Classical Introduction to Modern Number Theory*, Chapters 6 and 16, and Apostol, *Introduction to Analytic Number Theory*, Chapter 6.

### Reference

<?reference?>
