---
title: The field of fractions
kind: theory
modules: []
explains:
  E1: [IsFractionRing, FractionRing, FractionRing.field, IsFractionRing.lift, IsFractionRing.lift_algebraMap, IsFractionRing.lift_unique, IsFractionRing.injective, IsFractionRing.div_surjective, Rat.isFractionRing, FractionRing.algEquiv]
families: []
requires: [V06.C01, V06.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The field of fractions

### Overview

The rational numbers are built from the integers as fractions $a/b$ with $b \ne 0$, where $a/b = c/d$ means $a d = b c$. The same construction works for each integral domain $R$. It gives a field $\operatorname{Frac}(R)$ that contains $R$, and it is the smallest such field: each injective homomorphism of $R$ into a field extends in exactly one way to $\operatorname{Frac}(R)$. This universal property characterizes the field of fractions up to a unique isomorphism.

The section carries out the construction with all the checks, proves the universal property, and computes the fields of fractions of $\mathbb{Z}$, of $\mathbb{Z}[i]$ and of a field. The hypothesis that $R$ has no zero divisors is used at one place, the transitivity of the relation, and an example in $\mathbb{Z}/6$ shows that transitivity fails without it. Mathlib builds the field of fractions as a localization, which Volume 9 studies in general. Here it appears through its characteristic predicate `IsFractionRing`.

Throughout, $R$ is an integral domain.

### Definitions

**Definition (Field of fractions).** Let $R$ be an integral domain and let $P = \{(a, b) \in R \times R : b \ne 0\}$. On $P$ define $(a, b) \sim (c, d)$ if $a d = b c$. The *field of fractions* $\operatorname{Frac}(R)$ is the set $P/\sim$ of the classes, with the class of $(a, b)$ written $a/b$, and with the operations
$$\frac{a}{b} + \frac{c}{d} = \frac{a d + b c}{b d}, \qquad \frac{a}{b} \cdot \frac{c}{d} = \frac{a c}{b d}.$$
The *canonical map* is $\iota : R \to \operatorname{Frac}(R)$, $\iota(a) = a/1$.

The formulas are the school rules for fractions. Since $R$ is a domain, $b \ne 0$ and $d \ne 0$ give $b d \ne 0$, so the right hand sides are in $P$. In a ring with zero divisors this already fails.

**Definition (A field of fractions as a property).** Let $R$ be an integral domain and $K$ a field with an injective ring homomorphism $j : R \to K$. The pair $(K, j)$ is *a field of fractions* of $R$ if each element of $K$ has the form $j(a) j(b)^{-1}$ with $a, b \in R$, $b \ne 0$.

The construction gives one field of fractions. The universal property below shows that any two are isomorphic by a unique isomorphism that respects the maps from $R$. So it is safe to speak of *the* field of fractions, and to say that $\mathbb{Q}$ *is* the field of fractions of $\mathbb{Z}$, though $\mathbb{Q}$ may be built in another way.

::: mathlib
`IsFractionRing` · `Mathlib.RingTheory.Localization.FractionRing`

`IsFractionRing R K` is a proposition about a commutative ring `K` with an `Algebra R K` structure, that is, with a ring homomorphism `algebraMap R K` (Chapter 8). It says that `K` is the localization of `R` at the submonoid `nonZeroDivisors R`: the non-zero-divisors become units, each element is a fraction, and two fractions agree under the rule above, with a correction for zero divisors that disappears in a domain. It is a characteristic predicate. A theorem about fields of fractions is stated for every `K` with `[IsFractionRing R K]`, and then it applies to `ℚ`, to `FractionRing R` and to any other model.

<?decl IsFractionRing?>
:::

::: mathlib
`FractionRing` · `Mathlib.RingTheory.Localization.FractionRing`

The construction: `FractionRing R` is `Localization (nonZeroDivisors R)`, the localization of Volume 9, defined for each commutative ring. It is a field when `R` is a domain, by the instance `FractionRing.field`. For a ring with zero divisors it is the total ring of fractions, which is not a field in general.

<?decl FractionRing?>
:::

::: mathlib
`FractionRing.field` · `Mathlib.RingTheory.Localization.FractionRing`

The instance `Field (FractionRing A)` under `[IsDomain A]`.

<?decl FractionRing.field?>
:::

### Theorems and proofs

**Theorem (The relation is an equivalence).** Let $R$ be an integral domain. The relation $\sim$ on $P$ is an equivalence relation.

*Proof.* Reflexive: $a b = b a$, since $R$ is commutative. Symmetric: if $a d = b c$, then $c b = d a$. Transitive: let $(a, b) \sim (c, d)$ and $(c, d) \sim (e, f)$, so $a d = b c$ and $c f = d e$. Then
$$(a f) d = (a d) f = (b c) f = b (c f) = b (d e) = (b e) d.$$
So $(a f - b e) d = 0$. Since $d \ne 0$ and $R$ has no zero divisors, $a f = b e$, that is, $(a, b) \sim (e, f)$. $\square$

**Theorem (The operations are well defined).** Let $R$ be an integral domain. The sum and the product of classes in $\operatorname{Frac}(R)$ do not depend on the representatives.

*Proof.* By symmetry of the formulas in the two arguments, it is enough to change the first representative. Let $(a, b) \sim (a', b')$, so $a b' = a' b$, and let $(c, d) \in P$.

The sum. The claim is $(a d + b c, b d) \sim (a' d + b' c, b' d)$, that is,
$$(a d + b c)(b' d) = (b d)(a' d + b' c).$$
The left side is $a b' d^2 + b b' c d$. The right side is $a' b d^2 + b b' c d$. They are equal, since $a b' = a' b$.

The product. The claim is $(a c)(b' d) = (b d)(a' c)$. Both sides equal $(a b') c d = (a' b) c d$. $\square$

**Theorem (The field of fractions is a field).** Let $R$ be an integral domain. With the operations above, $\operatorname{Frac}(R)$ is a field with zero $0/1$ and one $1/1$. The map $\iota$ is an injective ring homomorphism, and $a/b = \iota(a) \iota(b)^{-1}$ for each $a/b$.

*Proof.* Plan: the commutative ring axioms follow from those of $R$ by computation on representatives; then inverses; then the claims on $\iota$.

First, a useful rule: $a/b = (a c)/(b c)$ for each $c \ne 0$, since $a (b c) = b (a c)$. So two fractions can be put over a common denominator, $a/b = (a d)/(b d)$ and $c/d = (b c)/(b d)$, and then
$$\frac{x}{s} + \frac{y}{s} = \frac{x s + s y}{s^2} = \frac{x + y}{s}.$$
With a common denominator, addition is addition of numerators. So the additive axioms of $\operatorname{Frac}(R)$ follow from those of $R$: for three fractions over a common denominator $s$, associativity and commutativity of the sum are those of the numerators, $0/1 = 0/s$ is neutral, and $(-x)/s$ is the negative of $x/s$. The product is associative and commutative with neutral element $1/1$, since numerators and denominators multiply separately. The distributive law, over a common denominator $s$:
$$\frac{x}{s}\left(\frac{y}{s} + \frac{z}{s}\right) = \frac{x (y + z)}{s^2} = \frac{x y + x z}{s^2} = \frac{x y}{s^2} + \frac{x z}{s^2}.$$

Next, $0 \ne 1$: the classes $0/1$ and $1/1$ are equal only if $0 \cdot 1 = 1 \cdot 1$, that is, $0 = 1$ in $R$, which is false in a domain. A class $a/b$ is $0$ if and only if $a \cdot 1 = b \cdot 0$, that is, $a = 0$. So if $a/b \ne 0$, then $a \ne 0$, $(b, a) \in P$, and $(a/b)(b/a) = (a b)/(b a) = 1/1$. So each nonzero element has an inverse, and $\operatorname{Frac}(R)$ is a field.

The map $\iota$ preserves sums and products, since $a/1 + c/1 = (a + c)/1$ and $(a/1)(c/1) = (a c)/1$, and $\iota(1) = 1/1$. It is injective: $a/1 = c/1$ means $a = c$. Finally, for $b \ne 0$, $\iota(a) \iota(b)^{-1} = (a/1)(1/b) = a/b$. $\square$

**Theorem (Universal property).** Let $R$ be an integral domain, let $L$ be a field and let $g : R \to L$ be an injective ring homomorphism. There is exactly one ring homomorphism $\bar g : \operatorname{Frac}(R) \to L$ with $\bar g \circ \iota = g$. It is $\bar g(a/b) = g(a) g(b)^{-1}$.

*Proof.* Well defined: if $b \ne 0$, then $g(b) \ne 0$ by injectivity, so $g(b)^{-1}$ exists. If $a/b = c/d$, then $a d = b c$, so $g(a) g(d) = g(b) g(c)$. Multiply by $g(b)^{-1} g(d)^{-1}$: $g(a) g(b)^{-1} = g(c) g(d)^{-1}$.

Homomorphism: $\bar g(1/1) = 1$, and
$$\bar g\left(\frac{a}{b} + \frac{c}{d}\right) = \frac{g(a) g(d) + g(b) g(c)}{g(b) g(d)} = \frac{g(a)}{g(b)} + \frac{g(c)}{g(d)},$$
where the fractions on the right are computed in the field $L$. The product is the same computation. Also $\bar g(\iota(a)) = g(a) g(1)^{-1} = g(a)$.

Uniqueness: let $\varphi : \operatorname{Frac}(R) \to L$ be a homomorphism with $\varphi \circ \iota = g$. For $b \ne 0$, $(a/b) \cdot \iota(b) = \iota(a)$. Apply $\varphi$: $\varphi(a/b) g(b) = g(a)$, so $\varphi(a/b) = g(a) g(b)^{-1} = \bar g(a/b)$. $\square$

::: mathlib
`IsFractionRing.lift` · `Mathlib.RingTheory.Localization.FractionRing`

The map $\bar g$: for `[IsFractionRing A K]`, a field `L` and `hg : Function.Injective g` with `g : A →+* L`, the term `IsFractionRing.lift hg : K →+* L`. The computation rule is `IsFractionRing.lift_algebraMap`, and the uniqueness is `IsFractionRing.lift_unique`.

<?decl IsFractionRing.lift?>
:::

::: mathlib
`IsFractionRing.lift_algebraMap` · `Mathlib.RingTheory.Localization.FractionRing`

The equation $\bar g(\iota(x)) = g(x)$, with `algebraMap A K` in the role of $\iota$.

<?decl IsFractionRing.lift_algebraMap?>
:::

**Corollary (Uniqueness of the field of fractions).** Let $(K, j)$ and $(K', j')$ be fields of fractions of $R$. There is exactly one isomorphism $\theta : K \to K'$ with $\theta \circ j = j'$.

*Proof.* The theorem holds for any field of fractions $(K, j)$ in place of the construction, with the same proof, since it only uses that each element of $K$ is $j(a) j(b)^{-1}$. Apply it to $j' : R \to K'$: there is a unique $\theta : K \to K'$ with $\theta \circ j = j'$. In the same way there is a unique $\theta' : K' \to K$ with $\theta' \circ j' = j$. Then $\theta' \circ \theta : K \to K$ satisfies $(\theta' \circ \theta) \circ j = j$, and so does the identity. By uniqueness, $\theta' \circ \theta = \mathrm{id}$. In the same way $\theta \circ \theta' = \mathrm{id}$. $\square$

**Corollary (The smallest field that contains $R$).** Let $R$ be a subring of a field $L$. The subfield of $L$ generated by $R$ is $\{a b^{-1} : a, b \in R, b \ne 0\}$, and it is a field of fractions of $R$.

*Proof.* Let $F = \{a b^{-1} : a, b \in R, b \ne 0\}$. It is the image of the homomorphism $\bar g$ for the inclusion $g : R \to L$, so it is a subring of $L$. It is closed under inverses: if $a b^{-1} \ne 0$, then $a \ne 0$ and $(a b^{-1})^{-1} = b a^{-1} \in F$. So $F$ is a subfield, and it contains $R$. Each subfield that contains $R$ contains each $a b^{-1}$, so contains $F$. Each element of $F$ has the required form, so $(F, g)$ is a field of fractions of $R$. $\square$

::: mathlib
`IsFractionRing.div_surjective` · `Mathlib.RingTheory.Localization.FractionRing`

Each element of a field of fractions `K` is `algebraMap A K x / algebraMap A K y` with `y` a non-zero-divisor. Together with the injectivity `IsFractionRing.injective`, this is the property of the definition above.

<?decl IsFractionRing.div_surjective?>
:::

::: mathlib
`FractionRing.algEquiv` · `Mathlib.RingTheory.Localization.FractionRing`

The isomorphism of the first corollary, from the construction to any model: `FractionRing A ≃ₐ[A] K`. The subscript `A` says that it commutes with the maps from `A`.

<?decl FractionRing.algEquiv?>
:::

### Examples

**Example (The rationals).** The field of fractions of $\mathbb{Z}$ is $\mathbb{Q}$. In the construction, $(1, 2) \sim (2, 4) \sim (-3, -6)$, and
$$\frac{1}{2} + \frac{1}{3} = \frac{1 \cdot 3 + 2 \cdot 1}{6} = \frac{5}{6}, \qquad \frac{2}{4} \cdot \frac{3}{9} = \frac{6}{36} = \frac{1}{6}.$$
In Mathlib, `ℚ` is not defined as `FractionRing ℤ`. It is a structure of a numerator and a positive denominator in lowest terms (Volume 2, Chapter 4), so that its arithmetic computes fast. The instance `Rat.isFractionRing : IsFractionRing ℤ ℚ` connects it to the general theory.

::: mathlib
`Rat.isFractionRing` · `Mathlib.RingTheory.Localization.FractionRing`

The instance that makes `ℚ` a field of fractions of `ℤ`. With it, `IsFractionRing.lift` gives the unique homomorphism from `ℚ` to any field of characteristic zero, which Chapter 4 uses.

<?decl Rat.isFractionRing?>
:::

**Example (The Gaussian integers).** The field of fractions of $\mathbb{Z}[i]$ is $\mathbb{Q}(i) = \{x + y i : x, y \in \mathbb{Q}\}$. By the second corollary it is the set of quotients $\alpha \beta^{-1}$ in $\mathbb{C}$ with $\alpha, \beta \in \mathbb{Z}[i]$, $\beta \ne 0$. Each such quotient is in $\mathbb{Q}(i)$: multiply above and below by $\bar \beta$,
$$\frac{\alpha}{\beta} = \frac{\alpha \bar \beta}{\beta \bar \beta} = \frac{\alpha \bar\beta}{N(\beta)},$$
with $\alpha \bar \beta \in \mathbb{Z}[i]$ and $N(\beta) \in \mathbb{Z}$ positive. Conversely $x + y i$ with $x = p/n$ and $y = q/n$ is $(p + q i)/n$. For example
$$\frac{3 + i}{1 + 2 i} = \frac{(3 + i)(1 - 2 i)}{5} = \frac{5 - 5 i}{5} = 1 - i,$$
so this quotient lies in $\mathbb{Z}[i]$, and $1 + 2 i$ divides $3 + i$ in $\mathbb{Z}[i]$. Chapter 6 uses this computation for division with remainder.

**Example (A field is its own field of fractions).** If $R = K$ is a field, then $\iota : K \to \operatorname{Frac}(K)$ is onto, since $a/b = \iota(a b^{-1})$. So $\iota$ is an isomorphism, and $\operatorname{Frac}(K) \cong K$.

**Example (Rational functions).** For a field $K$, the polynomial ring $K[X]$ of Chapter 5 is an integral domain, and its field of fractions is the field $K(X)$ of rational functions $f/g$. Volume 11 uses it. In Mathlib it is `RatFunc K`, built from `FractionRing K[X]`.

**Counterexample (Zero divisors break transitivity).** Let $R = \mathbb{Z}/6$ and use the same relation on pairs with nonzero second entry. Then $([0], [1]) \sim ([0], [2])$, since $0 \cdot 2 = 1 \cdot 0$. Also $([0], [2]) \sim ([3], [1])$, since $[0][1] = [0] = [2][3]$. But $([0], [1]) \not\sim ([3], [1])$, since $[0][1] = [0] \ne [3] = [1][3]$. The cancellation of $d = [2]$ in the proof of transitivity fails, because $[2]$ is a zero divisor. Also the product $[2] \cdot [3] = [0]$ of two denominators is not a valid denominator. Volume 9 repairs both defects for general rings by inverting only the non-zero-divisors, with a modified relation.

**Counterexample (The universal property needs injectivity).** The reduction $g : \mathbb{Z} \to \mathbb{Z}/5$ is a homomorphism into a field, and it is not injective. It has no extension to $\mathbb{Q}$: such an extension $\varphi$ would satisfy $\varphi(1/5) \cdot g(5) = \varphi(1) = 1$, but $g(5) = 0$. In fact there is no ring homomorphism $\mathbb{Q} \to \mathbb{Z}/5$ at all, since it would be injective by Section 2, and $\mathbb{Q}$ is infinite.

### The library around it

The field of fractions sits in Mathlib's theory of localization, in `Mathlib.RingTheory.Localization`. The general object is `IsLocalization M S`: the ring `S` is the localization of `R` at a submonoid `M`. A field of fractions is the case `M = nonZeroDivisors R`. The fraction with numerator `r` and denominator `s` is `IsLocalization.mk' K r s`, and `IsFractionRing.mk'_eq_div` rewrites it as a division in the field. Every lemma of localization applies to fields of fractions, and Volume 9 explains them. For this volume the useful names are:

- `algebraMap R K`, the canonical map $\iota$, with `IsFractionRing.injective`;
- `IsFractionRing.div_surjective`, each element is a fraction;
- `IsFractionRing.lift`, `IsFractionRing.lift_algebraMap`, `IsFractionRing.lift_unique`, the universal property;
- `FractionRing.algEquiv`, the uniqueness;
- `IsFractionRing.isDomain`, the fraction ring of a domain is a domain.

Common errors of a learner:

- Writing `FractionRing ℤ` where `ℚ` is meant. They are isomorphic and not equal. A theorem stated with `[IsFractionRing R K]` covers both.
- Forgetting the `Algebra R K` instance. `IsFractionRing R K` needs it, and for a subring of a field it comes from the inclusion.
- Using `IsFractionRing.lift` without the injectivity proof. The map does not exist otherwise, as the counterexample shows.
- Expecting `FractionRing R` to be a field for any commutative ring. The instance needs `[IsDomain R]`.

### Exercises

1. (A) In the construction of $\operatorname{Frac}(\mathbb{Z})$, check by the definition that $(2, 6) \sim (-5, -15)$, and compute $\frac{2}{6} + \frac{-1}{4}$.
2. (A) Show that $-(a/b) = (-a)/b = a/(-b)$ in $\operatorname{Frac}(R)$.
3. (A) Show that the field of fractions of $\mathbb{Z}[\sqrt 2]$ is $\mathbb{Q}(\sqrt 2)$. Hint: follow the example of $\mathbb{Z}[i]$ with the conjugate $a - b\sqrt 2$.
4. (B) Let $R \subseteq S$ be integral domains. Show that $\operatorname{Frac}(R)$ is isomorphic to a subfield of $\operatorname{Frac}(S)$.
5. (B) Show that each ring homomorphism $\mathbb{Q} \to L$ into a field is the unique extension of $\mathbb{Z} \to L$, so there is at most one homomorphism $\mathbb{Q} \to L$.
6. (B) Show that $\{a/2^k : a \in \mathbb{Z}, k \ge 0\}$ is a subring of $\mathbb{Q}$ whose field of fractions is $\mathbb{Q}$. So different domains can have the same field of fractions.
7. (B) Let $R$ be an integral domain with field of fractions $K$, and let $x \in K$. Show that the set $\{d \in R : d x \in R\}$ is an ideal of $R$, the ideal of denominators of $x$. Compute it for $R = \mathbb{Z}$ and $x = 3/4$.
8. (C) Let $R$ be an integral domain in which every element of $\operatorname{Frac}(R)$ is $a/b$ with $b$ a unit of $R$. Show that $R$ is a field.
9. (C) Construct the field of fractions of $\mathbb{Z}[X]$ and show that it is isomorphic to $\mathbb{Q}(X)$. Hint: both are fields of fractions of $\mathbb{Z}[X]$; apply the uniqueness corollary.

### Notes and history

Fractions of integers are as old as arithmetic, and the general construction is due to Steinitz, who formed the quotient field (Quotientenkörper) of an integral domain in 1910. Kronecker had worked with fields of rational functions in several variables in his 1882 memoir on algebraic quantities. The construction of $\mathbb{Q}$ from $\mathbb{Z}$ by pairs and an equivalence relation is the form of Landau's *Grundlagen der Analysis* (1930). The localization at an arbitrary multiplicative set is due to Grell (1927) and to Chevalley (1944).

In Mathlib the localization files were written by Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston and Anne Baanen. The characteristic predicates `IsLocalization` and `IsFractionRing` came in a later refactor, so that one theorem applies to all models of a localization. Before it, the theorems were stated for the construction only, and every application to `ℚ` needed a transfer.

### Reference

<?reference?>
