---
title: Units, zero divisors and integral domains
kind: theory
modules:
  - Mathlib.Algebra.Ring.Int.Units
  - Mathlib.Algebra.Ring.Units
  - Mathlib.Algebra.Ring.Invertible
  - Mathlib.Algebra.Ring.Regular
  - Mathlib.Algebra.Ring.NonZeroDivisors
  - Mathlib.Algebra.Ring.Torsion
  - Mathlib.Algebra.Ring.Associated
explains:
  E3: [IsDomain]
  E2: [Int.units_eq_one_or, Int.units_ne_iff_eq_neg, isDomain_iff_noZeroDivisors_and_nontrivial, NoZeroDivisors.to_isDomain, IsDomain.to_noZeroDivisors]
  E1: auto
families: []
requires: [V06.C01, V06.C02, V05.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Units, zero divisors and integral domains

### Overview

In the integers, a product of two nonzero numbers is nonzero, and only $1$ and $-1$ have an inverse. In $\mathbb{Z}/12$ both facts fail: $3 \cdot 4 = 0$, and $5 \cdot 5 = 1$. This section names the two phenomena. A *unit* is an element with a multiplicative inverse. A *zero divisor* is a nonzero element that multiplies some nonzero element to $0$. A ring with no zero divisors, and with $0 \ne 1$, is a *domain*. A commutative domain is an *integral domain*, and it is the setting of the arithmetic of the rest of the volume: the field of fractions in Section 3, the characteristic in Chapter 4, polynomials in Chapter 5 and factorization in Chapter 6.

The main results are: the units of a ring form a group; a unit is never a zero divisor; a ring is a domain if and only if the cancellation law holds; $1 + n$ is a unit for each nilpotent $n$. The examples compute the units of $\mathbb{Z}$, of the Gaussian integers $\mathbb{Z}[i]$, of a product ring and of $\mathbb{Z}[\sqrt 2]$, which has infinitely many.

All rings have a unit element $1$. They are not commutative unless the text says so.

### Definitions

**Definition (Unit).** Let $R$ be a ring. An element $u \in R$ is a *unit* if there is $v \in R$ with $u v = 1$ and $v u = 1$. The element $v$ is the *inverse* of $u$, written $u^{-1}$. The set of the units of $R$ is $R^\times$.

The inverse is unique. If $v$ and $w$ are both inverses of $u$, then $v = v (u w) = (v u) w = w$. In a commutative ring one of the two equations $u v = 1$ and $v u = 1$ is enough. In a noncommutative ring both are needed: the shift of sequences $(x_0, x_1, \dots) \mapsto (x_1, x_2, \dots)$ has a right inverse in the ring of linear maps, and no left inverse.

::: mathlib
`IsUnit` · `Mathlib.Algebra.Group.Units.Defs`

Mathlib has two forms of a unit. `IsUnit a` is a proposition: there is a bundled unit whose value is `a`. The type `Units R`, written `Rˣ`, is a structure with four fields: the value `val`, the inverse `inv`, and the proofs `val_inv : val * inv = 1` and `inv_val : inv * val = 1`. Both are defined for a monoid, so they are the units of Volume 5, Chapter 1, applied to the multiplicative monoid of the ring. Use `IsUnit` in a statement, and `Rˣ` when the inverse is data that later steps compute with. The bridge is `IsUnit.unit : IsUnit a → Rˣ`.

<?decl IsUnit?>
:::

**Definition (Zero divisor).** Let $R$ be a ring. A nonzero element $a \in R$ is a *zero divisor* if there is a nonzero $b \in R$ with $a b = 0$ or $b a = 0$.

**Definition (Domain, integral domain).** A ring $R$ is a *domain* if $0 \ne 1$ in $R$ and $R$ has no zero divisors: for all $a, b \in R$, $a b = 0$ implies $a = 0$ or $b = 0$. A commutative domain is an *integral domain*.

The condition $0 \ne 1$ excludes the zero ring $\{0\}$. The zero ring has no zero divisors, since it has no nonzero element. It is excluded because many theorems fail for it: for example, a domain should have a field of fractions, and a field has $0 \ne 1$. The same convention makes $1$ not a prime number.

::: mathlib
`IsDomain` · `Mathlib.Algebra.Ring.Defs`

`IsDomain R` is a class of propositions over a `Semiring R`. It is a mixin: it adds a property to the ring structure already present, and it has no data. Its two parents are `IsCancelMulZero R`, the cancellation law for nonzero factors, and `Nontrivial R`, which says $0 \ne 1$ in effect (there are two distinct elements). An integral domain in the textbook sense is `[CommRing R] [IsDomain R]`. Mathlib has no separate class for it, because the combination of two classes does the same work and avoids a third copy of every lemma.

<?decl IsDomain?>
:::

::: mathlib
`NoZeroDivisors` · `Mathlib.Algebra.GroupWithZero.Defs`

`NoZeroDivisors R` says `a * b = 0 → a = 0 ∨ b = 0`. It needs only a multiplication and a zero, so it applies also to the zero ring. The main lemma is `mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0`, a `simp` lemma. The cancellation lemma is `mul_left_cancel₀ : a ≠ 0 → a * b = a * c → b = c`.

<?decl NoZeroDivisors?>
:::

**Definition (Nilpotent element).** An element $n$ of a ring is *nilpotent* if $n^k = 0$ for some $k \ge 1$.

A nonzero nilpotent element is a zero divisor: if $k$ is the least exponent with $n^k = 0$, then $k \ge 2$, $n^{k-1} \ne 0$ and $n \cdot n^{k-1} = 0$. So a domain has no nonzero nilpotent element.

::: mathlib
`IsNilpotent` · `Mathlib.Algebra.GroupWithZero.Basic`

`IsNilpotent x` is `∃ n, x ^ n = 0`. The exponent $0$ is allowed in the definition, but `x ^ 0 = 1`, so `x ^ 0 = 0` holds only in the zero ring, where every element is nilpotent anyway.

<?decl IsNilpotent?>
:::

### Theorems and proofs

**Theorem (The unit group).** Let $R$ be a ring. The set $R^\times$ contains $1$, is closed under products and inverses, and is a group under the multiplication of $R$.

*Proof.* The element $1$ is a unit with inverse $1$. Let $u, v \in R^\times$. Then
$$(u v)(v^{-1} u^{-1}) = u (v v^{-1}) u^{-1} = u u^{-1} = 1,$$
and in the same way $(v^{-1} u^{-1})(u v) = 1$. So $u v \in R^\times$ with $(u v)^{-1} = v^{-1} u^{-1}$. The element $u^{-1}$ is a unit with inverse $u$, by the symmetry of the definition. The multiplication of $R$ is associative and $1$ is neutral, so the group axioms hold in $R^\times$. $\square$

**Theorem (Units are not zero divisors).** Let $u$ be a unit of a ring $R$. If $u a = 0$ or $a u = 0$, then $a = 0$.

*Proof.* If $u a = 0$, then $a = 1 \cdot a = (u^{-1} u) a = u^{-1} (u a) = u^{-1} \cdot 0 = 0$. The case $a u = 0$ is the same with $u^{-1}$ on the right. $\square$

So in any ring the units and the zero divisors are disjoint sets. In a finite commutative ring every nonzero element is one of the two (Exercise 6). In $\mathbb{Z}$ the element $2$ is neither.

**Theorem (Cancellation).** Let $R$ be a ring with $0 \ne 1$. Then $R$ is a domain if and only if the cancellation laws hold: for all $a, b, c \in R$ with $a \ne 0$, $a b = a c$ implies $b = c$, and $b a = c a$ implies $b = c$.

*Proof.* Let $R$ be a domain, let $a \ne 0$ and let $a b = a c$. Then $a (b - c) = a b - a c = 0$. Since $a \ne 0$ and $R$ has no zero divisors, $b - c = 0$, so $b = c$. The right law has the same proof with $(b - c) a = 0$.

Conversely, assume the cancellation laws. Let $a b = 0$ with $a \ne 0$. Then $a b = 0 = a \cdot 0$, and left cancellation gives $b = 0$. So $a b = 0$ implies $a = 0$ or $b = 0$. $\square$

The proof subtracts. In a semiring such as $\mathbb{N}$ there is no subtraction, and the two conditions are different in general. This is why Mathlib takes cancellation, not the absence of zero divisors, as the field of `IsDomain`: the definition then makes sense for semirings too.

::: mathlib
`isDomain_iff_noZeroDivisors_and_nontrivial` · `Mathlib.Algebra.Ring.Basic`

For a `Ring` the two forms agree: `IsDomain α ↔ NoZeroDivisors α ∧ Nontrivial α`. This is the theorem above. Note the hypothesis `Ring`, not `Semiring`: the proof needs subtraction.

<?decl isDomain_iff_noZeroDivisors_and_nontrivial?>
:::

::: mathlib
`NoZeroDivisors.to_isDomain` · `Mathlib.Algebra.Ring.Basic`

The direction that builds a domain. To prove that a ring is a domain, prove `NoZeroDivisors R` and `Nontrivial R` and apply this theorem. It is a theorem and not an instance, so it is applied by hand, often with `have := NoZeroDivisors.to_isDomain R`.

<?decl NoZeroDivisors.to_isDomain?>
:::

::: mathlib
`IsDomain.to_noZeroDivisors` · `Mathlib.Algebra.Ring.Basic`

The other direction is an instance. So in a domain the lemma `mul_eq_zero` is available with no extra work.

<?decl IsDomain.to_noZeroDivisors?>
:::

**Theorem (One plus a nilpotent is a unit).** Let $R$ be a ring and let $n \in R$ with $n^k = 0$ for some $k \ge 1$. Then $1 + n$ is a unit, with inverse
$$(1 + n)^{-1} = \sum_{j=0}^{k-1} (-n)^j = 1 - n + n^2 - \dots + (-1)^{k-1} n^{k-1}.$$

*Proof.* Let $s = \sum_{j=0}^{k-1} (-n)^j$. The powers of $n$ commute with $n$ and with $1$, so the telescoping computation of a geometric sum holds:
$$(1 + n) s = (1 - (-n)) \sum_{j=0}^{k-1} (-n)^j = \sum_{j=0}^{k-1} (-n)^j - \sum_{j=1}^{k} (-n)^j = 1 - (-n)^k.$$
Now $(-n)^k = (-1)^k n^k = 0$, so $(1 + n) s = 1$. The same computation with the factors in the other order gives $s (1 + n) = 1$. So $1 + n$ is a unit with inverse $s$. $\square$

::: mathlib
`IsNilpotent.isUnit_one_add` · `Mathlib.RingTheory.Nilpotent.Basic`

The theorem for a `Ring`, not only a commutative ring: `IsNilpotent r → IsUnit (1 + r)`. The form `IsNilpotent.isUnit_add_one` has `r + 1`. The general form for a unit plus a commuting nilpotent is in the same file.

<?decl IsNilpotent.isUnit_one_add?>
:::

**Theorem (Units of a product).** Let $R$ and $S$ be rings. An element $(a, b) \in R \times S$ is a unit if and only if $a \in R^\times$ and $b \in S^\times$. So $(R \times S)^\times = R^\times \times S^\times$ as groups.

*Proof.* The operations of $R \times S$ are componentwise, and $1 = (1, 1)$. If $(a, b)(c, d) = (1, 1)$ and $(c, d)(a, b) = (1, 1)$, then $a c = 1 = c a$ and $b d = 1 = d b$. So $a$ and $b$ are units. Conversely, if $a$ and $b$ are units, then $(a^{-1}, b^{-1})$ is an inverse of $(a, b)$. The equality of groups holds because the product of units is componentwise. $\square$

::: mathlib
`Prod.isUnit_iff` · `Mathlib.Algebra.Group.Prod`

`IsUnit x ↔ IsUnit x.1 ∧ IsUnit x.2`. The isomorphism of unit groups is `MulEquiv.prodUnits : (M × N)ˣ ≃* Mˣ × Nˣ`.

<?decl Prod.isUnit_iff?>
:::

**Theorem (Units of the integers).** The units of $\mathbb{Z}$ are $1$ and $-1$.

*Proof.* Both are units, since $1 \cdot 1 = 1$ and $(-1)(-1) = 1$. Let $u v = 1$ with $u, v \in \mathbb{Z}$. Then $|u| \cdot |v| = 1$ with $|u|, |v| \in \mathbb{N}$. Neither is $0$, so both are at least $1$, and if $|u| \ge 2$ then $|u| |v| \ge 2$. So $|u| = 1$ and $u = \pm 1$. $\square$

::: mathlib
`Int.units_eq_one_or` · `Mathlib.Algebra.Ring.Int.Units`

The statement for the bundled units: each `u : ℤˣ` is `1` or `-1`. For an integer with `IsUnit`, use `Int.isUnit_iff : IsUnit u ↔ u = 1 ∨ u = -1`.

<?decl Int.units_eq_one_or?>
:::

::: mathlib
`Int.units_ne_iff_eq_neg` · `Mathlib.Algebra.Ring.Int.Units`

The group $\mathbb{Z}^\times$ has two elements, so $u \ne v$ means $u = -v$. The lemma is used to split a case on two units.

<?decl Int.units_ne_iff_eq_neg?>
:::

### Examples

**Example (Units and zero divisors of $\mathbb{Z}/12$).** By Volume 2, Chapter 6, the class $[a]$ is a unit of $\mathbb{Z}/12$ if and only if $\gcd(a, 12) = 1$. So $(\mathbb{Z}/12)^\times = \{[1], [5], [7], [11]\}$, and each of them is its own inverse: $25$, $49$ and $121$ are $1$ modulo $12$. The other nonzero classes are zero divisors:
$$[2][6] = [3][4] = [4][3] = [6][2] = [8][3] = [9][4] = [10][6] = [0].$$
The class $[6]$ is nilpotent, since $36 = 3 \cdot 12$. The theorem on nilpotents gives that $[1] + [6] = [7]$ is a unit with inverse $[1] - [6] = [-5] = [7]$. This agrees with $[7]^2 = [49] = [1]$.

**Example (Units of the Gaussian integers).** Let $\mathbb{Z}[i] = \{a + b i : a, b \in \mathbb{Z}\} \subseteq \mathbb{C}$. Put $N(a + b i) = a^2 + b^2 = |a + b i|^2$. Then $N(z w) = N(z) N(w)$, since $|z w| = |z| |w|$. If $z w = 1$ in $\mathbb{Z}[i]$, then $N(z) N(w) = 1$ in $\mathbb{N}$, so $N(z) = 1$ and $a^2 + b^2 = 1$. The integer solutions are $(\pm 1, 0)$ and $(0, \pm 1)$. So $\mathbb{Z}[i]^\times = \{1, -1, i, -i\}$, a cyclic group of order $4$ generated by $i$. The ring $\mathbb{Z}[i]$ is an integral domain, because it is a subring of the field $\mathbb{C}$ and a subring of a domain is a domain. Chapter 6 studies its arithmetic.

**Example (Infinitely many units in $\mathbb{Z}[\sqrt 2]$).** Let $\mathbb{Z}[\sqrt 2] = \{a + b \sqrt 2 : a, b \in \mathbb{Z}\} \subseteq \mathbb{R}$ and $N(a + b \sqrt 2) = (a + b\sqrt 2)(a - b \sqrt 2) = a^2 - 2 b^2$. The map $a + b \sqrt 2 \mapsto a - b \sqrt 2$ is a ring homomorphism of $\mathbb{Z}[\sqrt 2]$ to itself, because $\sqrt 2$ and $-\sqrt 2$ have the same square. So $N(x y) = N(x) N(y)$. If $x$ is a unit, then $N(x) N(x^{-1}) = N(1) = 1$ in $\mathbb{Z}$, so $N(x) = \pm 1$. Conversely, if $N(x) = \pm 1$, then $x \cdot (\pm (a - b \sqrt 2)) = 1$, so $x$ is a unit. The element $u = 1 + \sqrt 2$ has $N(u) = 1 - 2 = -1$, so it is a unit, with inverse $-1 + \sqrt 2$. Since $u > 1$ as a real number, $1 < u < u^2 < u^3 < \cdots$, and the powers $u^n$ are distinct units. So $\mathbb{Z}[\sqrt 2]^\times$ is infinite. Units of this ring correspond to solutions of Pell's equation $a^2 - 2 b^2 = \pm 1$, a subject of Volume 12.

**Example (Matrices).** In the ring $M_2(\mathbb{R})$ of real $2 \times 2$ matrices, a matrix is a unit if and only if its determinant is nonzero (Volume 7). The matrices
$$E = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}, \quad F = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}, \quad N = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$$
satisfy $E F = 0$ and $N^2 = 0$. So $E$, $F$ and $N$ are zero divisors, and $N$ is nilpotent. The theorem on nilpotents gives
$$(I + N)^{-1} = I - N = \begin{pmatrix} 1 & -1 \\ 0 & 1 \end{pmatrix},$$
which a direct product confirms.

**Counterexample (Cancellation needs a domain).** In $\mathbb{Z}/6$, $[2][1] = [2] = [2][4]$, but $[1] \ne [4]$. The factor $[2]$ is a zero divisor, since $[2][3] = [0]$. In the product ring $\mathbb{Z} \times \mathbb{Z}$, $(1, 0)(0, 1) = (0, 0)$, so a product of two domains is not a domain. The units of $\mathbb{Z} \times \mathbb{Z}$ are the four pairs $(\pm 1, \pm 1)$, by the theorem on products.

**Counterexample (The sum of nilpotents needs commutativity).** In a commutative ring, the sum of two nilpotent elements is nilpotent (Exercise 5). In $M_2(\mathbb{R})$ let $N$ be as above and $M = N^{T}$. Both square to $0$, but
$$(N + M)^2 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}^2 = I,$$
so $N + M$ is a unit and not nilpotent. The proof of Exercise 5 uses the binomial theorem, which needs $N M = M N$, and here $N M = E \ne F = M N$.

### The library around it

The units of a ring are the units of its multiplicative monoid, so the whole API of Volume 5 applies: `Units.val_mul`, `Units.inv_mul`, `IsUnit.mul`, `isUnit_iff_exists_inv`, and the map `Units.map` of a monoid homomorphism. A ring homomorphism sends units to units, by `IsUnit.map`. In a group with zero, such as a field, `isUnit_iff_ne_zero` says that the units are the nonzero elements; Section 2 uses it.

The zero divisor API is in `Mathlib.Algebra.GroupWithZero.Defs` and `Basic`: `mul_eq_zero`, `mul_ne_zero`, `mul_self_eq_zero`, `pow_eq_zero_iff`, and the cancellation lemmas `mul_left_cancel₀`, `mul_right_cancel₀` and `mul_right_injective₀`. Each holds under `NoZeroDivisors` or `IsCancelMulZero`, so each applies to a domain by instance search. A subring of a domain is a domain by the instance for subrings, and the image of an injective ring homomorphism into a domain gives a domain by `Function.Injective.isDomain`.

The set of the non-zero-divisors of a commutative ring is the submonoid `nonZeroDivisors R`, written `R⁰`. It is the denominator set of the field of fractions in Section 3.

Several small modules connect these notions to the ring operations. `Mathlib.Algebra.Ring.Units` gives the negation of units: $-u$ is a unit (`Units.instNeg`, `IsUnit.neg`, `isUnit_neg_one`), `IsUnit.sub_iff` says that $x - y$ is a unit if and only if $y - x$ is, and `RingHom.isUnit_map` sends units to units. It also has the rules for the division by a unit $a /_p u = a u^{-1}$, such as `Units.divp_add_divp_same` and `Units.divp_add_divp`. `Mathlib.Algebra.Ring.Invertible` does the same for the data-carrying class `Invertible a` with the inverse `⅟a`: `invertibleNeg` and `invOf_neg` for $-a$, `invOf_add_invOf` for $a^{-1} + b^{-1} = a^{-1}(a + b) b^{-1}$, and `invOf_two_add_invOf_two` for $\tfrac12 + \tfrac12 = 1$.

`Mathlib.Algebra.Ring.Regular` links regular elements and zero divisors: in a ring, an element $k$ with $k x = 0 \Rightarrow x = 0$ is left cancellable, by `isLeftRegular_of_non_zero_divisor`, and without zero divisors each nonzero element is regular, by `IsRegular.of_ne_zero'`, so `NoZeroDivisors.toIsCancelMulZero` gives cancellation. `Mathlib.Algebra.Ring.NonZeroDivisors` shows that the elements of `nonZeroDivisors R` are exactly the regular elements, by `isRegular_iff_mem_nonZeroDivisors`, and that they cancel, by `mul_cancel_left_mem_nonZeroDivisors` and `mul_cancel_right_mem_nonZeroDivisors`. In a finite ring each non-zero-divisor is a unit, by `isUnit_iff_mem_nonZeroDivisors_of_finite`, since multiplication by it is an injective map of a finite set to itself. `Mathlib.Algebra.Ring.Torsion` shows that a monoid homomorphism from a ring to a monoid without torsion sends $-1$ to $1$, by `MonoidHom.map_neg_one`, since $f(-1)^2 = f(1) = 1$. `Mathlib.Algebra.Ring.Associated` shows that $a$ and $-a$ are associated, with `Associated.neg_left`, `Associated.neg_right` and `Associated.neg_neg`.

Common errors of a learner:

- Writing `[IntegralDomain R]`. The class does not exist. Write `[CommRing R] [IsDomain R]`.
- Forgetting `Nontrivial`. A lemma that needs `IsDomain` does not apply to a ring that has only `NoZeroDivisors`, because the zero ring has no zero divisors but is not a domain.
- Confusing `IsUnit a` with `a ≠ 0`. They agree in a field and not in `ℤ`: `(2 : ℤ) ≠ 0` but `¬ IsUnit (2 : ℤ)`.
- Coercing a unit back to `R` by hand. A term `u : Rˣ` is used in `R` as `(u : R)`, which is `u.val`. The inverse in `R` is `(u⁻¹ : Rˣ)` coerced, not `(u : R)⁻¹`, which exists only in a division ring.

### Exercises

1. (A) List the units, the zero divisors and the nilpotent elements of $\mathbb{Z}/8$. Check that $1 + n$ is a unit for each nilpotent $n$. Hint: the nilpotents are the even classes.
2. (A) Show that a subring of a domain is a domain, and that $\mathbb{Z}[\sqrt{-5}] \subseteq \mathbb{C}$ is an integral domain. Find its units. Hint: use $N(a + b\sqrt{-5}) = a^2 + 5 b^2$.
3. (A) Let $R$ be a ring with $0 \ne 1$. Show that $0$ is not a unit.
4. (B) Show that $u + n$ is a unit when $u$ is a unit, $n$ is nilpotent and $u n = n u$. Hint: write $u + n = u (1 + u^{-1} n)$ and show that $u^{-1} n$ is nilpotent.
5. (B) In a commutative ring, show that the sum of two nilpotent elements is nilpotent. Hint: if $a^k = 0$ and $b^m = 0$, expand $(a + b)^{k + m - 1}$ by the binomial theorem.
6. (B) Let $R$ be a finite commutative ring and $a \in R$ nonzero. Show that $a$ is a unit or a zero divisor. Hint: if $a$ is not a zero divisor, the map $x \mapsto a x$ is injective, so it is surjective.
7. (B) Show that $\mathbb{Z}[\sqrt 2]^\times = \{\pm u^n : n \in \mathbb{Z}\}$ with $u = 1 + \sqrt 2$. Hint: for a unit $x > 0$, choose $n$ with $u^n \le x < u^{n+1}$, and show that $y = x u^{-n}$ is a unit with $1 \le y < u$; then show $y = 1$ by bounds on $a$ and $b$ in $y = a + b\sqrt 2$.
8. (C) Show that in a ring, if $1 - a b$ is a unit, then $1 - b a$ is a unit. Hint: guess the inverse $1 + b (1 - a b)^{-1} a$ from the formal series, then check it.

### Notes and history

The words come from the nineteenth century theory of algebraic integers. Dirichlet studied the units of the rings $\mathbb{Z}[\sqrt d]$ and proved in 1846 that the unit group of the ring of integers of a number field is finitely generated, with a rank that he computed; Volume 12 states his unit theorem. Kronecker and Dedekind used the term *unit* (Einheit) for these invertible algebraic integers. The German term *Integritätsbereich*, the source of *integral domain*, goes back to Kronecker, and it first meant a domain of algebraic integers. Noether and her school gave the abstract definition in the 1920s. The term *nilpotent* is due to Benjamin Peirce, in his *Linear Associative Algebra* of 1870.

In Mathlib, integral domains were first a bundled class that extended the commutative ring structure. The class was later changed into the mixin `IsDomain` over `Semiring`, so that one ring can be a domain, an ordered ring and a normed ring at once without a diamond of structures, and so that noncommutative domains use the same class. The file `Mathlib.Algebra.Ring.Int.Units` holds the facts on $\mathbb{Z}^\times$ that need the ring structure of $\mathbb{Z}$.

### Reference

<?reference?>
