---
title: The rationals
kind: theory
modules:
  - Mathlib.Data.Rat.Init
  - Mathlib.Data.Rat.Defs
  - Mathlib.Data.Rat.Lemmas
  - Mathlib.Data.NNRat.Defs
explains:
  E3: [NNRat, Rat.den_dvd]
  E2: [Rat.mkRat_eq_divInt, Rat.num_dvd, Rat.den_eq_one_iff, Rat.num_div_eq_of_coprime, Rat.den_div_eq_of_coprime, NNRat.coe_add, Rat.toNNRat]
  E1: auto
families: []
requires: [V02.C03]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V02/C04/Examples.lean
  - MathlibHandbook/V02/C04/Exercises.lean
  - MathlibHandbook/V02/C04/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The rationals

### Overview

The rational numbers add the solutions of all equations $b x = a$ with $a, b \in \mathbb{Z}$, $b \neq 0$. A textbook builds $\mathbb{Q}$ as classes of pairs $(a, b)$ with $b \neq 0$, where $(a, b) \sim (c, d)$ if $a d = b c$. Each class has one member in lowest terms with a positive denominator, and the core of Lean uses this member as the definition.

This section gives the construction by classes, the theorem that each class has exactly one member in lowest terms, the structure of Lean with the functions `mkRat` and `Rat.divInt`, and the type `ℚ≥0`. The next section studies the order of $\mathbb{Q}$.

### Definitions

**Definition (Fractions).** On the set $\mathbb{Z} \times (\mathbb{Z} \setminus \{0\})$ define $(a, b) \sim (c, d)$ if $a d = b c$. The class of $(a, b)$ is written $a / b$, and $\mathbb{Q}$ is the set of the classes.

The relation is reflexive and symmetric. It is transitive: from $a d = b c$ and $c f = d e$ follows $a d f = b c f = b d e$, so $d (a f - b e) = 0$. Since $d \neq 0$ and $\mathbb{Z}$ is an integral domain, $a f = b e$.

**Definition (The operations).** For two classes put

$$\frac{a}{b} + \frac{c}{d} = \frac{a d + b c}{b d}, \qquad \frac{a}{b} \cdot \frac{c}{d} = \frac{a c}{b d}, \qquad -\frac{a}{b} = \frac{-a}{b}, \qquad \left(\frac{a}{b}\right)^{-1} = \frac{b}{a} \text{ for } a \neq 0.$$

The denominators $b d$ are not zero, again because $\mathbb{Z}$ is an integral domain. The integer $n$ is the class $n / 1$.

**Definition (Lowest terms).** A pair $(a, b)$ is in lowest terms if $b > 0$ and $\gcd(a, b) = 1$.

**Definition (The rationals in Lean).** The core of Lean defines `ℚ` as a structure with four fields: `num : ℤ`, `den : ℕ`, `den_nz : den ≠ 0` and `reduced : num.natAbs.Coprime den`. The value of `q` is $q.\mathrm{num} / q.\mathrm{den}$.

*Remark.* The sign of `q` is the sign of the numerator. Two terms of `ℚ` are equal when their numerators and their denominators are equal, because the two proof fields are propositions.

**Definition (Making a fraction).** For $n \in \mathbb{Z}$ and $d \in \mathbb{N}$, `mkRat n d` is the fraction $n / d$ in lowest terms. For $n, d \in \mathbb{Z}$, `Rat.divInt n d`, with the notation `n /. d`, is the same fraction. At $d = 0$ both have the junk value $0$, as the field division `(n : ℚ) / d` does.

::: mathlib
`Rat.mkRat_eq_divInt` · `Mathlib.Data.Rat.Defs`

The two functions make the same fraction: `mkRat n d = Rat.divInt n ↑d`. The lemma moves a goal from `mkRat` to the form of the library.

<?decl Rat.mkRat_eq_divInt?>
:::

**Definition (The nonnegative rationals).** `NNRat` is the subtype `{q : ℚ // 0 ≤ q}`, with the notation `ℚ≥0`. The cast `(q : ℚ)` takes a term of `ℚ≥0` to its value. The function `Rat.toNNRat q` is $\max(q, 0)$, so its value at a negative number is the junk value $0$.

::: mathlib
`NNRat` · `Mathlib.Data.Rat.Init`

A term is a pair of a rational number and a proof that it is not negative. The type is a semifield, and its subtraction is truncated, as in `ℕ`. The lemmas of the cast to `ℚ` have the prefix `NNRat.coe_`, for example `NNRat.coe_add`, and `norm_cast` uses them.

<?decl NNRat?>
:::

::: mathlib
`Rat.toNNRat` · `Mathlib.Data.NNRat.Defs`

The value is `⟨max q 0, _⟩`. So `Rat.toNNRat (-1) = 0`. A lemma that removes `toNNRat` has the hypothesis `0 ≤ q`.

<?decl Rat.toNNRat?>
:::

### Theorems and proofs

**Theorem (The operations are well defined).** The sum, the product, the negation and the inverse of classes do not depend on the choice of the pairs.

*Proof.* Let $a b' = a' b$. Both formulas are symmetric, so it is enough to change the first argument. For the sum, $(a d + b c) b' d = a b' d^2 + b b' c d = a' b d^2 + b b' c d = (a' d + b' c) b d$. For the product, $a c \cdot b' d = a' c \cdot b d$ is $c d$ times the hypothesis. The negation is direct. For the inverse, $a \neq 0$ gives $a' \neq 0$, and $b a' = b' a$ is the hypothesis. $\square$

The field axioms then follow from the ring axioms of $\mathbb{Z}$ by computation on representatives, and $n \mapsto n / 1$ is an injective ring map $\mathbb{Z} \to \mathbb{Q}$.

**Theorem (Lowest terms).** Each class has exactly one member in lowest terms.

*Proof.* Existence. Let $(c, d)$ be a member. If $d < 0$, replace it by $(-c, -d)$. Let $g = \gcd(c, d) > 0$, $a = c / g$ and $b = d / g$. Then $b > 0$ and $a d = b c$. A common divisor $e > 0$ of $a$ and $b$ gives the common divisor $e g$ of $c$ and $d$, so $e = 1$.

Uniqueness. Let $(a, b)$ and $(a', b')$ be two members in lowest terms. Then $a b' = a' b$. So $b \mid a b'$. Since $\gcd(b, a) = 1$, Euclid's lemma in its form for coprime numbers gives $b \mid b'$. In the same way $b' \mid b$. Both are positive, so $b = b'$. Then $a b = a' b$ and $b \neq 0$ give $a = a'$. $\square$

**Theorem (Numerator and denominator of a fraction).** Let $a, b \in \mathbb{Z}$ with $b \neq 0$, and let $q = a / b$ with numerator $n$ and denominator $d$. Then $d \mid b$ and $n \mid a$. If $b > 0$ and $\gcd(a, b) = 1$, then $n = a$ and $d = b$.

*Proof.* By the proof of the theorem on lowest terms, $(n, d) = (\pm a / g, |b| / g)$ with $g = \gcd(a, b)$, where the sign is the sign of $b$. So $b = \pm g d$ and $a = \pm g n$, and both divisibilities hold. If $b > 0$ and $\gcd(a, b) = 1$, then $(a, b)$ is in lowest terms, and the uniqueness part gives $(n, d) = (a, b)$. $\square$

For $b = 0$ the fraction is the junk value $0 / 1$. Then $d \mid b$ still holds, but $n \mid a$ fails for $a \neq 0$.

::: mathlib
`Rat.den_dvd` · `Mathlib.Data.Rat.Lemmas`

The statement is `↑(Rat.divInt a b).den ∣ b`, with no hypothesis on `b`. The lemma `Rat.num_dvd` has the hypothesis `b ≠ 0`.

<?decl Rat.den_dvd?>
:::

::: mathlib
`Rat.num_div_eq_of_coprime` · `Mathlib.Data.Rat.Lemmas`

For `0 < b` and `a.natAbs.Coprime b.natAbs`, `Rat.num_div_eq_of_coprime` gives `(a / b : ℚ).num = a`, and `Rat.den_div_eq_of_coprime` gives `((a / b : ℚ).den : ℤ) = b`. They read the numerator of a fraction with variables.

<?decl Rat.num_div_eq_of_coprime?>
:::

**Proposition (Integers among the rationals).** A rational number $q$ is in the image of $\mathbb{Z}$ if and only if its denominator is $1$.

*Proof.* If the denominator is $1$, then $q = n / 1$ is the image of its numerator $n$. Conversely, if $q = m / 1$ for some $m \in \mathbb{Z}$, then $(m, 1)$ is in lowest terms, so it is the member of $q$ in lowest terms, and the denominator is $1$. $\square$

::: mathlib
`Rat.den_eq_one_iff` · `Mathlib.Data.Rat.Defs`

The statement is `r.den = 1 ↔ ↑r.num = r`, with the cast `Int.cast : ℤ → ℚ`.

<?decl Rat.den_eq_one_iff?>
:::

### Examples

**Example (Lowest terms).** For $6 / 4$, $\gcd(6, 4) = 2$, so the numerator is $3$ and the denominator is $2$. For $6 / -4$, change the signs first: the numerator is $-3$ and the denominator is $2$.

<?lean MathlibHandbook/V02/C04/Examples.lean#num_den?>

**Example (A sum).** The formula gives $\frac{1}{6} + \frac{1}{10} = \frac{16}{60}$. The gcd of $16$ and $60$ is $4$, so the sum in lowest terms is $\frac{4}{15}$. The formula does not give lowest terms, so Lean reduces after each operation.

**Example (Two ways to make a fraction).**

<?lean MathlibHandbook/V02/C04/Examples.lean#mkRat?>

**Example (Numerator over denominator).** The lemma `Rat.num_div_den` is in `Mathlib.Algebra.Ring.Rat`, because the division is the division of the field.

<?lean MathlibHandbook/V02/C04/Examples.lean#num_div_den?>

**Example (An integer).**

<?lean MathlibHandbook/V02/C04/Examples.lean#den_eq_one?>

**Counterexample (The relation needs b ≠ 0).** With the pairs $(a, 0)$, $(1, 0) \sim (0, 0)$ and $(0, 0) \sim (0, 1)$, but $(1, 0) \not\sim (0, 1)$. So the relation is not transitive. The step from $d (a f - b e) = 0$ fails for $d = 0$.

**Example (The cast of ℚ≥0).**

<?lean MathlibHandbook/V02/C04/Examples.lean#nnrat?>

### The library around it

The structure `Rat` and the functions `mkRat` and `Rat.divInt` are in the core of Lean. Mathlib adds `Mathlib.Data.Rat.Init` with `NNRat`, `Mathlib.Data.Rat.Defs` with the basic lemmas (`Rat.den_ne_zero`, `Rat.num_ne_zero`, `Rat.add_divInt`), and `Mathlib.Data.Rat.Lemmas` with the divisibility lemmas. The field structure is `Rat.instField`, and `Rat.isFractionRing : IsFractionRing ℤ ℚ` connects `ℚ` to the general field of fractions. The tactic `norm_num` proves equations of rational literals.

### Exercises

1. (A) Give the values of `(0 : ℚ).den`, `(-3 / 6 : ℚ).num`, `mkRat 5 0` and `Rat.toNNRat (-2)` in Mathlib. *Hint.* Use lowest terms and the junk values.
2. (A) Compute $\frac{5}{12} - \frac{7}{18}$ in lowest terms, first with the formula of the definition and then with $\gcd(12, 18)$. *Hint.* The result has denominator $36$.
3. (B) Show that the product of two fractions in lowest terms $\frac{a}{b}$ and $\frac{c}{d}$ is in lowest terms if $\gcd(a, d) = \gcd(c, b) = 1$. *Hint.* A prime that divides $a c$ and $b d$ divides one factor of each.
4. (B) Show that the map from `ℚ≥0` to `ℚ` is injective and keeps the order. *Hint.* A subtype has equality of the values.
5. (L) Prove that $1/2 + 1/3 = 5/6$ in `ℚ`. The solution is `half_add_third`.
6. (L) Prove that a rational number with denominator $1$ is the cast of an integer. The solution is `den_of_den_eq_one`.
7. (L) Prove that the product of two terms of `ℚ≥0` is not negative in `ℚ`. The solution is `nnrat_mul_nonneg`.

### Notes and history

Egyptian and Babylonian texts compute with fractions. The field of fractions of an integral domain is the general form of the construction. The structure in lowest terms is the choice of the core of Lean, because it makes computation fast and equality decidable.

### Reference

<?reference?>
