---
title: Localization at a submonoid
kind: theory
modules:
  - Mathlib.RingTheory.Localization.Defs
explains:
  E3: [IsLocalization, "IsLocalization.mk'", IsLocalization.lift]
  E2: [IsLocalization.map_units, IsLocalization.surj, IsLocalization.exists_of_eq, "IsLocalization.mk'_spec", "IsLocalization.mk'_surjective", "IsLocalization.mk'_eq_iff_eq", IsLocalization.lift_eq, IsLocalization.lift_unique, IsLocalization.lift_comp, IsLocalization.map_eq_zero_iff, "IsLocalization.mk'_eq_zero_iff", IsLocalization.algEquiv, Localization.isLocalization, "Localization.mk_eq_mk'", Localization.add_mk, IsLocalization.Away, IsLocalization.Away.invSelf, IsLocalization.Away.mul_invSelf, IsLocalization.Away.algebraMap_isUnit, IsLocalization.Away.surj, IsLocalization.Away.lift, Localization.AtPrime, IsLocalization.AtPrime, Ideal.primeCompl, IsLocalization.injective, IsLocalization.uniqueOfZeroMem, IsLocalization.to_map_eq_zero_iff]
  E1: auto
families: []
requires: [V09.C01, V06.C02, V06.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Localization at a submonoid

### Overview

Localization makes the elements of a multiplicative set $S$ invertible. For a domain and $S = R \setminus \{0\}$ it gives the field of fractions of Volume 6, Chapter 3. In a ring with zero divisors the relation needs one extra factor: $a/s = b/t$ when $u (a t - b s) = 0$ for some $u \in S$. Mathlib works with a predicate that says when a homomorphism $R \to A$ is a localization at $S$, and the section proves that its three conditions characterize $S^{-1} R$. Rings are commutative with $1$, and multiplicative sets are as in Chapter 1, Section 2.

### Definitions

**Definition (The localization).** Let $S$ be a multiplicative subset of $R$. On $R \times S$ define $(a, s) \sim (b, t)$ if $u (a t - b s) = 0$ for some $u \in S$. Write $a/s$ for the class of $(a, s)$, and $S^{-1} R$ for the set of classes. Put
$$\frac{a}{s} + \frac{b}{t} = \frac{a t + b s}{s t}, \qquad \frac{a}{s} \cdot \frac{b}{t} = \frac{a b}{s t},$$
and let $\iota : R \to S^{-1} R$ be $a \mapsto a/1$.

**Definition (Standard cases).** For $f \in R$, the localization at $\{1, f, f^2, \dots\}$ is written $R_f$ or $R[1/f]$. For a prime ideal $\mathfrak{p}$, the set $R \setminus \mathfrak{p}$ is multiplicative, and the localization at it is written $R_{\mathfrak{p}}$.

**Definition (Localization map).** A ring homomorphism $g : R \to A$ is a localization at $S$ if

1. $g(s)$ is a unit of $A$ for each $s \in S$;
2. each $z \in A$ has the form $z = g(a) g(s)^{-1}$ with $a \in R$, $s \in S$;
3. if $g(a) = g(b)$, then $u a = u b$ for some $u \in S$.

::: mathlib
`IsLocalization` · `Mathlib.RingTheory.Localization.Defs`

`IsLocalization M S` is a predicate on an `R`-algebra `S` and a `Submonoid` `M` of `R`. Its three fields are the conditions of the definition for `algebraMap R S`: `IsLocalization.map_units`, `IsLocalization.surj` and `IsLocalization.exists_of_eq`. The construction of the text is `Localization M` of Volume 5, with the instance `Localization.isLocalization`. A theorem stated with `IsLocalization` applies to every model.

<?decl IsLocalization?>
:::

### Theorems and proofs

**Theorem (The relation).** The relation $\sim$ is an equivalence relation.

*Proof.* Reflexivity and symmetry are clear. Let $u (a t - b s) = 0$ and $w (b v - c t) = 0$ with $u, w \in S$. Multiply the first equation by $w v$ and the second by $u s$:
$$u w \, a t v = u w \, b s v, \qquad u w \, b v s = u w \, c t s.$$
So $u w t \, a v = u w t \, c s$, that is, $(t u w)(a v - c s) = 0$, and $t u w \in S$. $\square$

**Theorem (The ring $S^{-1} R$).** The operations are well defined and make $S^{-1} R$ a commutative ring with zero $0/1$ and unit $1/1$. The map $\iota$ is a ring homomorphism, and $\iota(s)$ is a unit with inverse $1/s$ for each $s \in S$.

*Proof.* Let $a/s = a'/s'$, with $u (a s' - a' s) = 0$. Then
$$u \big( (a t + b s) s' t - (a' t + b s') s t \big) = t^2 \, u (a s' - a' s) = 0,$$
$$u \big( a b \, s' t - a' b \, s t \big) = b t \, u (a s' - a' s) = 0.$$
So the sum and the product do not depend on the first representative, and by symmetry not on the second. First, $a/s = (v a)/(v s)$ for $v \in S$, since $1 \cdot (a v s - v a s) = 0$. Each ring axiom is an identity between fractions. Bring both sides to a common denominator with this rule. Then the numerators agree by the axioms of $R$. For example
$$\frac{a}{s} \Big( \frac{b}{t} + \frac{c}{v} \Big) = \frac{a b v + a c t}{s t v}, \qquad \frac{a b}{s t} + \frac{a c}{s v} = \frac{s (a b v + a c t)}{s \cdot s t v}.$$
Clearly $\iota(a + b) = (a + b)/1 = a/1 + b/1$ and $\iota(a b) = \iota(a) \iota(b)$. Finally $(s/1)(1/s) = s/s = 1/1$. $\square$

**Theorem (Kernel).** For $a \in R$ and $s \in S$, $a/s = 0$ if and only if $u a = 0$ for some $u \in S$. Consequently:

1. $S^{-1} R = 0$ if and only if $0 \in S$;
2. $\iota$ is injective if and only if no element of $S$ is a zero divisor.

*Proof.* $a/s = 0/1$ means $u (a \cdot 1 - 0 \cdot s) = u a = 0$ for some $u \in S$. (1) $S^{-1} R = 0$ means $1/1 = 0$, that is, $u \cdot 1 = 0$ for some $u \in S$. (2) $\ker \iota = \{ a : u a = 0 \text{ for some } u \in S \}$. It is $0$ exactly when $u a = 0$ with $u \in S$ forces $a = 0$. $\square$

**Theorem (Universal property).** Let $g : R \to A$ be a ring homomorphism such that $g(s)$ is a unit for each $s \in S$. Then there is exactly one ring homomorphism $h : S^{-1} R \to A$ with $h \circ \iota = g$, namely $h(a/s) = g(a) g(s)^{-1}$.

*Proof.* If $u (a t - b s) = 0$, then $g(u) (g(a) g(t) - g(b) g(s)) = 0$. Since $g(u)$, $g(s)$, $g(t)$ are units, $g(a) g(s)^{-1} = g(b) g(t)^{-1}$. So $h$ is well defined. It sends $1/1$ to $1$, and
$$h\Big(\frac{a t + b s}{s t}\Big) = (g(a) g(t) + g(b) g(s)) g(s)^{-1} g(t)^{-1} = h\Big(\frac{a}{s}\Big) + h\Big(\frac{b}{t}\Big).$$
Products are similar. For uniqueness, let $h'$ be a homomorphism with $h' \circ \iota = g$. From $(a/s) \cdot \iota(s) = \iota(a)$ follows $h'(a/s) \, g(s) = g(a)$, so $h'(a/s) = g(a) g(s)^{-1}$. $\square$

::: mathlib
`IsLocalization.lift` · `Mathlib.RingTheory.Localization.Defs`

For `[IsLocalization M S]` and `hg : ∀ y : M, IsUnit (g y)`, `IsLocalization.lift hg : S →+* P` is the map $h$. The rules are `IsLocalization.lift_eq : lift hg (algebraMap R S x) = g x`, `IsLocalization.lift_comp` and `IsLocalization.lift_unique`.

<?decl IsLocalization.lift?>
:::

**Theorem (Characteristic property).** The map $\iota : R \to S^{-1} R$ is a localization at $S$. Conversely, if $g : R \to A$ is a localization at $S$, then the map $h$ of the universal property is an isomorphism $S^{-1} R \cong A$ with $h \circ \iota = g$.

*Proof.* For $\iota$: condition (1) is the theorem on the ring. For (2), $a/s = \iota(a) \iota(s)^{-1}$. For (3), $\iota(a) = \iota(b)$ means $u (a - b) = 0$ for some $u \in S$, by the theorem on the kernel.

Let $g$ be a localization. Condition (1) gives $h$. By (2), $h$ is surjective. If $h(a/s) = g(a) g(s)^{-1} = 0$, then $g(a) = g(0)$, so $u a = 0$ for some $u \in S$ by (3), and $a/s = 0$. So $h$ is injective. $\square$

By the uniqueness in the universal property, any two localizations at $S$ are isomorphic by a unique isomorphism over $R$.

::: mathlib
`IsLocalization.mk'` · `Mathlib.RingTheory.Localization.Defs`

`IsLocalization.mk' S x y` is the fraction $x/y$ in any localization `S`. The rules are `IsLocalization.mk'_spec : mk' S x y * algebraMap R S y = algebraMap R S x`, `IsLocalization.mk'_surjective` and `IsLocalization.mk'_eq_iff_eq`. In `Localization M`, `Localization.mk_eq_mk'` relates `Localization.mk` to it, and `Localization.add_mk` is the rule for sums. The kernel theorem is `IsLocalization.map_eq_zero_iff`, `IsLocalization.to_map_eq_zero_iff` and `IsLocalization.mk'_eq_zero_iff`. Part (1) gives `IsLocalization.uniqueOfZeroMem`, and part (2) is `IsLocalization.injective`. The isomorphism of two models is `IsLocalization.algEquiv`.

<?decl IsLocalization.mk'?>
:::

**Theorem (Localization at an element).** $R_f = 0$ if and only if $f$ is nilpotent. Each element of $R_f$ has the form $a / f^n$, and $a/f^n = 0$ if and only if $f^m a = 0$ for some $m$.

*Proof.* Apply the kernel theorem to $S = \{1, f, f^2, \dots\}$, which contains $0$ exactly when $f$ is nilpotent. $\square$

::: mathlib
`IsLocalization.Away` · `Mathlib.RingTheory.Localization.Away.Basic`

`IsLocalization.Away x S` abbreviates `IsLocalization (Submonoid.powers x) S`. The rules include `IsLocalization.Away.invSelf`, `IsLocalization.Away.mul_invSelf`, `IsLocalization.Away.algebraMap_isUnit`, `IsLocalization.Away.surj` and `IsLocalization.Away.lift`. For a prime `P`, `Ideal.primeCompl P` is $R \setminus P$, `IsLocalization.AtPrime S P` is the predicate, and `Localization.AtPrime P` is the model.

<?decl IsLocalization.Away?>
:::

### Examples

**Example (Subrings of $\mathbb{Q}$).** Let $R$ be a domain and $0 \notin S$. Then no element of $S$ is a zero divisor, so $\iota$ is injective and $S^{-1} R$ is the subring $\{ a/s \}$ of the field of fractions. For $R = \mathbb{Z}$ and a prime $p$, this gives
$$\mathbb{Z}_{(p)} = \{ a/b \in \mathbb{Q} : p \nmid b \}, \qquad \mathbb{Z}[1/p] = \{ a/p^n : a \in \mathbb{Z}, n \ge 0 \}.$$
The two rings are different: $1/3 \in \mathbb{Z}_{(2)}$ and $1/3 \notin \mathbb{Z}[1/2]$, while $1/2 \in \mathbb{Z}[1/2]$ and $1/2 \notin \mathbb{Z}_{(2)}$.

**Counterexample (The factor $u$ is needed).** Let $R = \mathbb{Z}/6$ and $S = \{1, 2, 4\}$, a multiplicative set. Under the naive relation $a t = b s$, $(0, 1) \sim (0, 2)$ since $0 = 0$, and $(0, 2) \sim (3, 4)$ since $0 \cdot 4 = 0 = 3 \cdot 2$. But $(0, 1) \not\sim (3, 4)$, since $0 \cdot 4 = 0 \ne 3 = 3 \cdot 1$. So the naive relation is not transitive. With the factor $u = 2$, $2 (0 \cdot 4 - 3 \cdot 1) = -6 = 0$, so $0/1 = 3/4$ in $S^{-1} R$.

Now compute $S^{-1} R$. The kernel of $\iota$ is the set of $r$ with $2 r = 0$ or $4 r = 0$, that is, $\{0, 3\}$. Also $\iota(2)^2 = \iota(4) = \iota(1)$, since $4 - 1 = 3$ lies in the kernel. So $\iota(2)$ is its own inverse, each $a/s$ equals $\iota(a s)$, and $\iota$ is surjective. Hence $S^{-1} R \cong (\mathbb{Z}/6)/\{0, 3\} \cong \mathbb{Z}/3$.

### The library around it

The predicate and the basic API sit in `Mathlib.RingTheory.Localization.Defs`, and the field of fractions is `IsFractionRing R K := IsLocalization (nonZeroDivisors R) K`. Common errors:

- A lemma on `IsLocalization M S` needs the instance `[IsLocalization M S]`. For `Localization M` it is found automatically, but for a concrete ring it must be proved, usually by its three fields.
- `IsLocalization.mk' S x y` takes `y : M`, an element of the submonoid, not of `R`.

### Exercises

1. (A) Show that $\mathbb{Z}[1/6]$ is the localization of $\mathbb{Z}$ at $S = \{2^i 3^j : i, j \ge 0\}$.
2. (A) Let $R = k \times k$ for a field $k$ and $f = (1, 0)$. Show $R_f \cong k$. Hint: $f \cdot (0, b) = 0$, and $f$ is idempotent.
3. (B) Show that a localization of a reduced ring is reduced. Hint: from $u a^n = 0$ deduce $(u a)^n = 0$.
4. (B) Show $(R_f)_{g/1} \cong R_{f g}$. Hint: check the three conditions for $R \to R_{f g}$ composed in two steps.
5. (C) Show $R_f \cong R[x]/(f x - 1)$. Hint: check the three conditions for $R \to R[x]/(f x - 1)$. For (3), if $a = (f x - 1) q$ with $q = \sum_{i \le m} q_i x^i$, compare coefficients to get $q_i = f^i q_0$ and $f^{m + 1} q_0 = 0$.
6. (C) Let $\bar{S}$ be the set of $r \in R$ that divide some element of $S$. Show that $\bar{S}$ is multiplicative and $S^{-1} R \cong \bar{S}^{-1} R$. Hint: if $r r' = s \in S$, then $\iota(r) \iota(r') \iota(s)^{-1} = 1$.

### Notes and history

The construction with the extra factor in the relation is the one of Atiyah and Macdonald, Chapter 3. The characteristic predicate lets rings such as $\mathbb{Q}$ or $\mathbb{Z}_{(p)}$, built in other ways, count as localizations with no transport.

### Reference

<?reference?>
