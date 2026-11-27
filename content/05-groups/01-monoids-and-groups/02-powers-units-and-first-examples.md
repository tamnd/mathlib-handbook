---
title: Powers, units and the first examples
kind: theory
modules:
  - Mathlib.Algebra.Group.Units.Defs
  - Mathlib.Algebra.Group.Commute.Defs
  - Mathlib.GroupTheory.SpecificGroups.Dihedral
explains:
  E3: [Units]
  E2: [IsUnit, Units.ext, pow_add, pow_mul, zpow_add, Commute, Commute.mul_pow, DihedralGroup, DihedralGroup.r_mul_sr, DihedralGroup.card]
  E1: auto
families: []
requires: [V01.C04, V01.C06]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V05/C01/Examples.lean
  - MathlibHandbook/V05/C01/Exercises.lean
  - MathlibHandbook/V05/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Powers, units and the first examples

### Overview

The axioms of a group become useful only with examples. This section gives the tools to compute in a group and the first families of groups. It starts with the powers of an element. In a monoid the power $a^n$ is defined for $n \in \mathbb{N}$, and in a group it extends to $n \in \mathbb{Z}$. The laws of exponents hold, but the law $(a b)^n = a^n b^n$ needs that $a$ and $b$ commute.

The second topic is the group of units of a monoid. Each monoid $M$ contains a group: the elements that have a two-sided inverse. This one construction gives the group $\{1, -1\}$ of units of $\mathbb{Z}$, the groups $(\mathbb{Z}/n)^\times$ of number theory, the invertible matrices and the bijections of a set. The main theorem of the section says which classes modulo $n$ are units: the classes of the integers prime to $n$.

The last topic is the dihedral group $D_n$, the group of the symmetries of a regular polygon with $n$ sides. It is the first family of groups that are not commutative, and the later chapters use it as a test case for each new notion.

### Definitions

**Definition (Natural power).** Let $M$ be a monoid and let $a \in M$. The power $a^n$ for $n \in \mathbb{N}$ is defined by recursion: $a^0 = 1$ and $a^{n+1} = a^n \cdot a$.

**Definition (Integer power).** Let $G$ be a group and let $a \in G$. For $n \in \mathbb{N}$ the power $a^n$ is the natural power, and $a^{-n} = (a^n)^{-1}$.

For $n = 0$ the two clauses agree, because $1^{-1} = 1$. In additive notation the power $a^n$ is the multiple $n a$, and the definition says $0 a = 0$, $(n + 1) a = n a + a$ and $(-n) a = -(n a)$.

::: mathlib
`zpow_add` · `Mathlib.Algebra.Group.Basic`

The integer power `a ^ n` with `n : ℤ` is a field of `DivInvMonoid`, with the default value `zpowRec`. The default sends `Int.negSucc n`, the integer $-(n+1)$, to `(a ^ (n + 1))⁻¹`. The lemma `zpow_natCast` says that the integer power at a natural number is the natural power, and `zpow_neg` says $a^{-n} = (a^n)^{-1}$. A cast from `ℕ` to `ℤ` in the exponent is a common source of trouble: `a ^ (n : ℤ)` and `a ^ n` are different terms, and `zpow_natCast` moves between them.

<?decl zpow_add?>
:::

**Definition (Commuting elements).** Two elements $a$ and $b$ of a monoid commute if $a b = b a$.

::: mathlib
`Commute` · `Mathlib.Algebra.Group.Semigroup`

The predicate `Commute a b` unfolds to `SemiconjBy a b b`, which is `a * b = b * a`. It is a definition, not a class, so a proof of it is an argument of a lemma. The namespace `Commute` has the lemmas that need only two commuting elements, not a commutative monoid: `Commute.mul_pow`, `Commute.mul_zpow`, `Commute.pow_right` and others.

<?decl Commute?>
:::

**Definition (Unit).** Let $M$ be a monoid. An element $a \in M$ is a unit if there is $b \in M$ with $a b = 1$ and $b a = 1$. The set of the units is $M^\times$.

By the lemma on left and right inverses of the previous section, the element $b$ is unique. It is the inverse $a^{-1}$ of the unit $a$.

::: mathlib
`Units` · `Mathlib.Algebra.Group.Units.Defs`

The type `Units M`, with the notation `Mˣ`, is a structure with four fields: the value `val`, the inverse `inv`, and the two proofs `val_inv : val * inv = 1` and `inv_val : inv * val = 1`. A unit is not an element of `M` with a property. It is a new term that carries its inverse. The coercion `↑u : M` gives the value. The instance `Units.instGroup` makes `Mˣ` a group. This design makes the inverse a function on `Mˣ` with no side condition.

<?decl Units?>
:::

::: mathlib
`IsUnit` · `Mathlib.Algebra.Group.Units.Defs`

The predicate `IsUnit a` says that there is `u : Mˣ` with `↑u = a`. Use it to state that an element of `M` is invertible, and use `Units` to compute with the inverse. The term `h.unit` turns a proof `h : IsUnit a` into the unit. The lemma `isUnit_iff_exists_inv` gives the one-sided form in a monoid of the class `IsDedekindFiniteMonoid`, which contains each commutative monoid.

<?decl IsUnit?>
:::

**Definition (Dihedral group).** Let $n \ge 3$. The dihedral group $D_n$ is the group of the symmetries of a regular polygon with $n$ sides, under composition. Let $r$ be the rotation by the angle $2\pi/n$, and let $s$ be a reflection in a line through the center and a vertex.

The polygon has $n$ vertices, and a symmetry permutes them and keeps two adjacent vertices adjacent. A symmetry is fixed by the image $k$ of the vertex $0$ and by the image of the vertex $1$, which is $k + 1$ or $k - 1$. So $D_n$ has at most $2n$ elements. The elements $r^k$ and $s r^k$ for $k = 0, \dots, n-1$ are $2n$ distinct symmetries: the $r^k$ keep the orientation and the $s r^k$ reverse it. So $|D_n| = 2n$. The relations are $r^n = 1$, $s^2 = 1$ and $s r s = r^{-1}$, so $r^k s = s r^{-k}$.

::: mathlib
`DihedralGroup` · `Mathlib.GroupTheory.SpecificGroups.Dihedral`

Mathlib defines `DihedralGroup n` as an inductive type with two constructors `r i` and `sr i` for `i : ZMod n`. The term `r i` is the rotation $r^i$, and `sr i` is the reflection $s r^i$. The product is defined by four formulas on the constructors, so a product of two concrete elements computes. The definition works for each `n`. For `n = 0` it gives the infinite dihedral group, because `ZMod 0` is `ℤ`.

<?decl DihedralGroup?>
:::

### Theorems and proofs

**Theorem (Laws of exponents in a monoid).** Let $M$ be a monoid, $a \in M$ and $m, n \in \mathbb{N}$. Then $a^{m+n} = a^m a^n$ and $a^{m n} = (a^m)^n$.

*Proof.* Fix $m$ and prove the first law by induction on $n$. For $n = 0$, both sides are $a^m$, because $a^0 = 1$. Assume $a^{m+n} = a^m a^n$. Then
$$a^{m + (n+1)} = a^{(m+n)+1} = a^{m+n} a = (a^m a^n) a = a^m (a^n a) = a^m a^{n+1}.$$
For the second law, use induction on $n$ again. For $n = 0$, both sides are $1$. Assume $a^{m n} = (a^m)^n$. Then, by the first law,
$$a^{m(n+1)} = a^{m n + m} = a^{m n} a^m = (a^m)^n a^m = (a^m)^{n+1}.$$
$\square$

A consequence: two powers of the same element commute, since $a^m a^n = a^{m+n} = a^{n+m} = a^n a^m$.

::: mathlib
`pow_add` · `Mathlib.Algebra.Group.Monoid`

The first law in a monoid. The partner `pow_succ` is the recursion $a^{n+1} = a^n a$, and `pow_succ'` is the other form $a^{n+1} = a a^n$.

<?decl pow_add?>
:::

::: mathlib
`pow_mul` · `Mathlib.Algebra.Group.Monoid`

The second law with the factors of the exponent in the order $a^{m n} = (a^m)^n$. The form `pow_mul'` gives $a^{m n} = (a^n)^m$.

<?decl pow_mul?>
:::

**Theorem (Laws of exponents in a group).** Let $G$ be a group, $a \in G$ and $m, n \in \mathbb{Z}$. Then $a^{m+n} = a^m a^n$.

*Proof.* The plan has three steps. First $a^{k+1} = a^k a$ for each $k \in \mathbb{Z}$. Then $a^{k-1} = a^k a^{-1}$ for each $k \in \mathbb{Z}$. Last, an induction on $n$ in both directions.

Step 1. For $k \ge 0$ the equation is the definition of the natural power. Let $k = -j$ with $j \ge 1$. The two natural powers $a^{j-1}$ and $a$ commute, and $a^j = a \, a^{j-1}$. By the inverse of a product, $(a^j)^{-1} = (a^{j-1})^{-1} a^{-1}$. So
$$a^{-j} a = (a^{j-1})^{-1} a^{-1} a = (a^{j-1})^{-1} = a^{-(j-1)} = a^{k+1}.$$

Step 2. Apply step 1 to $k - 1$: $a^k = a^{k-1} a$. Multiply on the right by $a^{-1}$. Then $a^k a^{-1} = a^{k-1}$.

Step 3. Fix $m$. For $n = 0$ both sides are $a^m$. If the law holds for $n$, then by step 1
$$a^{m + n + 1} = a^{m+n} a = a^m a^n a = a^m a^{n+1},$$
so it holds for $n + 1$. If it holds for $n$, then by step 2
$$a^{m + n - 1} = a^{m+n} a^{-1} = a^m a^n a^{-1} = a^m a^{n-1},$$
so it holds for $n - 1$. Both directions from $0$ reach each integer. $\square$

**Theorem (Power of a product).** Let $M$ be a monoid, and let $a, b \in M$ commute. Then $(a b)^n = a^n b^n$ for each $n \in \mathbb{N}$.

*Proof.* First, $b$ commutes with $a^n$. For $n = 0$ this is $b \cdot 1 = 1 \cdot b$. If $b a^n = a^n b$, then $b a^{n+1} = b a^n a = a^n b a = a^n a b = a^{n+1} b$. Now prove the claim by induction. For $n = 0$ both sides are $1$. If $(a b)^n = a^n b^n$, then
$$(a b)^{n+1} = (a b)^n (a b) = a^n b^n a b = a^n (b^n a) b = a^n (a b^n) b = a^{n+1} b^{n+1}.$$
The fourth equality uses that $a$ commutes with $b^n$, which is the first claim with the roles of $a$ and $b$ exchanged. $\square$

::: mathlib
`Commute.mul_pow` · `Mathlib.Algebra.Group.Commute.Defs`

The theorem above, with the hypothesis `h : Commute a b`. Use it as `h.mul_pow n`. In a commutative monoid the lemma `mul_pow` has no hypothesis. The integer form is `Commute.mul_zpow`.

<?decl Commute.mul_pow?>
:::

**Theorem (The units are a group).** Let $M$ be a monoid. Then $M^\times$ is a group under the product of $M$.

*Proof.* There are four points to check. First, the product of two units is a unit. Let $a, b \in M^\times$. Then
$$(a b)(b^{-1} a^{-1}) = a (b b^{-1}) a^{-1} = a a^{-1} = 1, \qquad (b^{-1} a^{-1})(a b) = b^{-1} (a^{-1} a) b = b^{-1} b = 1.$$
So $a b$ is a unit with inverse $b^{-1} a^{-1}$. Second, $1$ is a unit, with $1 \cdot 1 = 1$. Third, the product is associative on $M^\times$, because it is associative on $M$. Fourth, if $a$ is a unit, then $a^{-1}$ is a unit with inverse $a$, since the two equations $a a^{-1} = 1$ and $a^{-1} a = 1$ are symmetric in $a$ and $a^{-1}$. So $M^\times$ is a monoid in which each element has an inverse. $\square$

::: mathlib
`Units.ext` · `Mathlib.Algebra.Group.Units.Defs`

Two units with the same value are equal. The inverse is unique, so the field `inv` adds no information, and this lemma proves it. Use `Units.ext` to reduce an equation in `Mˣ` to an equation in `M`, and then `Units.val_mul` to compute the value of a product.

<?decl Units.ext?>
:::

**Theorem (Units modulo $n$).** Let $n \ge 1$ and $a \in \mathbb{Z}$. The class of $a$ in $\mathbb{Z}/n$ is a unit of the monoid $(\mathbb{Z}/n, \cdot)$ if and only if $\gcd(a, n) = 1$.

*Proof.* Assume $\gcd(a, n) = 1$. By the theorem of Bézout there are integers $u, v$ with $u a + v n = 1$. In $\mathbb{Z}/n$ the class of $v n$ is $0$, so $\bar u \, \bar a = \bar 1$. The ring $\mathbb{Z}/n$ is commutative, so also $\bar a \, \bar u = \bar 1$, and $\bar a$ is a unit. Conversely, assume $\bar a \, \bar u = \bar 1$ for some $u$. Then $n$ divides $a u - 1$, so $a u - 1 = n w$ for some $w \in \mathbb{Z}$. Let $d = \gcd(a, n)$. Then $d$ divides $a u - n w = 1$, so $d = 1$. $\square$

So $(\mathbb{Z}/n)^\times$ has $\varphi(n)$ elements, where $\varphi$ is the totient function of Euler. For a prime $p$ each nonzero class is a unit, and $(\mathbb{Z}/p)^\times$ has $p - 1$ elements.

**Theorem (The dihedral group is not commutative).** For $n \ge 3$, the elements $r$ and $s$ of $D_n$ do not commute.

*Proof.* From $s r s = r^{-1}$ and $s^2 = 1$ the product $r s$ is $s r^{-1}$. If $r s = s r$, then $s r^{-1} = s r$, and cancellation gives $r^{-1} = r$, so $r^2 = 1$. But $r$ is the rotation by $2\pi/n$, and $r^2$ is the rotation by $4\pi/n$, which is not the identity for $n \ge 3$. $\square$

::: mathlib
`DihedralGroup.r_mul_sr` · `Mathlib.GroupTheory.SpecificGroups.Dihedral`

One of the four rules of the product: `r i * sr j = sr (j - i)`, that is, $r^i \cdot s r^j = s r^{j-i}$. The others are `r_mul_r`, `sr_mul_r` and `sr_mul_sr`. The last one says `sr i * sr j = r (j - i)`. With `i = j` it gives that each reflection has order $2$. The lemma `DihedralGroup.not_commutative` is the theorem above for `n ≠ 1` and `n ≠ 2`.

<?decl DihedralGroup.r_mul_sr?>
:::

::: mathlib
`DihedralGroup.card` · `Mathlib.GroupTheory.SpecificGroups.Dihedral`

The order $2n$ of `DihedralGroup n`, with `Fintype.card`. It needs `NeZero n`, because `DihedralGroup 0` is infinite.

<?decl DihedralGroup.card?>
:::

### Examples

**Example (Powers modulo $7$).** In $(\mathbb{Z}/7)^\times = \{1, 2, 3, 4, 5, 6\}$ compute the powers of $3$. Each step multiplies the previous power by $3$ and reduces modulo $7$:
$$3^1 = 3, \quad 3^2 = 9 = 2, \quad 3^3 = 6, \quad 3^4 = 18 = 4, \quad 3^5 = 12 = 5, \quad 3^6 = 15 = 1.$$
So each unit modulo $7$ is a power of $3$. The inverse of $3$ is $3^5 = 5$, and indeed $3 \cdot 5 = 15 = 1$. The negative powers follow: $3^{-2} = (3^2)^{-1} = 2^{-1} = 4$, and $3^{-2} = 3^{6-2} = 3^4 = 4$ agrees with the law of exponents.

**Example (Units modulo $12$).** The integers between $0$ and $11$ that are prime to $12$ are $1, 5, 7, 11$. So $(\mathbb{Z}/12)^\times = \{1, 5, 7, 11\}$. The squares are $25 = 1$, $49 = 1$ and $121 = 1$ modulo $12$. The other products are $5 \cdot 7 = 35 = 11$, $5 \cdot 11 = 55 = 7$ and $7 \cdot 11 = 77 = 5$. This is the table of the Klein four group of the previous section, with $e = 1$, $a = 5$, $b = 7$, $c = 11$. The class $2$ is not a unit: $2 u$ is even, and an even integer is never $1$ modulo $12$.

**Example (Units of other monoids).** The units of $(\mathbb{Z}, \cdot)$ are $1$ and $-1$, because $a b = 1$ in $\mathbb{Z}$ forces $|a| = 1$. The units of the monoid of $2 \times 2$ real matrices are the matrices with nonzero determinant, by the formula for the inverse of a $2 \times 2$ matrix. They form the group $\mathrm{GL}_2(\mathbb{R})$. The units of the monoid of the maps $X \to X$ are the bijections, because a map has a two-sided inverse exactly when it is a bijection. They form the symmetric group of $X$, the subject of Chapter 7.

**Example (The dihedral group $D_4$).** The square has the eight symmetries $1, r, r^2, r^3, s, s r, s r^2, s r^3$. Compute two products with the rule $r^i s = s r^{-i}$:
$$(s r)(s r^2) = s (r s) r^2 = s (s r^{-1}) r^2 = s^2 r = r, \qquad (s r^2)(s r) = s (r^2 s) r = s s r^{-2} r = r^{-1} = r^3.$$
The two products differ, so $D_4$ is not commutative. In the notation of Mathlib, the first product is `sr 1 * sr 2 = r (2 - 1) = r 1`, as the rule `sr_mul_sr` says.

**Counterexample (The power of a product needs commuting factors).** In $D_3$, take $a = r$ and $b = s$. The product $r s = s r^{-1}$ is a reflection, so $(r s)^2 = 1$. But $r^2 s^2 = r^2 \neq 1$. So $(a b)^2 \neq a^2 b^2$. The theorem on the power of a product fails without the hypothesis that $a$ and $b$ commute.

### The library around it

The laws of exponents come in families with a fixed pattern of names. For the natural power in a monoid: `pow_zero`, `pow_one`, `pow_succ`, `pow_add`, `pow_mul`, `one_pow`, `pow_mul_comm`. For the integer power in a group: the same names with `zpow` in place of `pow`, such as `zpow_zero`, `zpow_one`, `zpow_add`, `zpow_mul`, `zpow_neg`, and the casts `zpow_natCast` and `zpow_neg_one`. The inverse of a power is `inv_pow`. Each has an additive copy for the multiples: `add_nsmul`, `mul_nsmul`, `add_zsmul`, `neg_zsmul`.

The units have a family of coercion lemmas with the prefix `Units.val_`: `Units.val_mul`, `Units.val_one`, `Units.val_inv_eq_inv_val`. The predicate `IsUnit` has `IsUnit.mul`, `isUnit_one` and `IsUnit.unit`. The units of `ZMod n` are described in `Mathlib.Data.ZMod.Basic`, with `ZMod.unitOfCoprime` and `ZMod.isUnit_iff_coprime`. The units of `ℤ` are `1` and `-1` by `Int.units_eq_one_or`. The concrete groups of Mathlib are in `Mathlib.GroupTheory.SpecificGroups`: the dihedral group, the quaternion group `QuaternionGroup n` of order $4n$, the cyclic groups and the alternating groups.

### Exercises

1. (A) Compute the powers of $2$ in $(\mathbb{Z}/11)^\times$, and show that each unit modulo $11$ is a power of $2$.
2. (A) List the elements of $(\mathbb{Z}/8)^\times$ and show that each of them has square $1$.
3. (A) In $D_4$, compute $(s r^3)(r^2)$ and $(r^2)(s r^3)$ with the rule $r^i s = s r^{-i}$.
4. (B) Let $G$ be a group with $(a b)^2 = a^2 b^2$ for all $a, b$. Show that $G$ is commutative. Hint: expand $a b a b = a a b b$ and cancel.
5. (B) Show that $(a^{-1})^n = (a^n)^{-1}$ in a group, for $n \in \mathbb{N}$. Hint: $a^{-1}$ and $a$ commute, so use the theorem on the power of a product with $a \cdot a^{-1}$.
6. (B) Show that the elements $r^k$ and $s r^k$ for $0 \le k < n$ are $2n$ distinct elements of $D_n$. Hint: a rotation keeps the cyclic order of the vertices, and a reflection reverses it.
7. (B) Let $M$ be a monoid and let $a \in M$ have a left inverse $b$ and a right inverse $c$. Show that $a$ is a unit.
8. (C) Show that $(\mathbb{Z}/2^k)^\times$ is not of the form $\{a^m : m \in \mathbb{Z}\}$ for any $a$, when $k \ge 3$. Hint: show that $1$, $-1$, $2^{k-1} + 1$ and $2^{k-1} - 1$ all have square $1$, and that a group of powers of one element has at most two elements with square $1$.

### Notes and history

The units of $\mathbb{Z}/n$ and the powers modulo a prime are older than the notion of a group. Euler studied them in the 1760s, and Gauss gave the full theory of the powers modulo $n$ in the *Disquisitiones Arithmeticae* of 1801. Gauss proved there that $(\mathbb{Z}/p)^\times$ is the set of the powers of one element, a primitive root, for each prime $p$. The dihedral groups appear in the work of Klein on the symmetries of the regular solids, in the 1870s.

In Mathlib, the structure `Units` dates from the first years of the library in Lean 3. The choice to bundle the inverse with the value was made early and kept: it makes the group instance on `Mˣ` a plain structure. The dihedral group in `Mathlib.GroupTheory.SpecificGroups.Dihedral` was written by Shing Tak Lam in 2020, with the inductive type that makes its products compute.

### Reference

<?reference?>
