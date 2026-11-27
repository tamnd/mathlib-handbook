---
title: Degree and the tower law
kind: theory
modules:
  - Mathlib.FieldTheory.Tower
  - Mathlib.FieldTheory.IntermediateField.Algebraic
  - Mathlib.FieldTheory.Relrank
  - Mathlib.FieldTheory.Finiteness
explains:
  E3: [IntermediateField.finrank_dvd_of_le_right, IntermediateField.relfinrank, IntermediateField.relfinrank_mul_relfinrank, FiniteDimensional.right]
  E2: [FiniteDimensional.left, Module.Finite.right, IntermediateField.finrank_lt_of_gt, IntermediateField.finrank_bot_mul_relfinrank, IntermediateField.relfinrank_eq_one_iff, IntermediateField.finiteDimensional_left, IntermediateField.finiteDimensional_right, IntermediateField.finrank_le_of_le_right, IntermediateField.finrank_dvd_of_le_left, Module.card_eq_pow_finrank, IsNoetherian.iff_fg, IntermediateField.relfinrank_bot_left, IntermediateField.relfinrank_top_left]
  E1: auto
families: []
requires: [V07.C02, V06.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Degree and the tower law

### Overview

An extension $L/K$ makes $L$ a vector space over $K$. Its dimension is the degree $[L:K]$. The degree is the first number attached to an extension, and the tower law makes it useful: for fields $K \subseteq L \subseteq M$,
$$[M:K] = [M:L]\,[L:K].$$
So the degree of an intermediate field divides the degree of the whole extension. For example, $\sqrt 2$ does not lie in a field of degree $3$ over $\mathbb{Q}$.

The section defines the degree, proves the tower law with a product basis, and derives its corollaries. It ends with the relative degree of two intermediate fields, which Mathlib uses to state the tower law inside one lattice. The section needs Section 1 of this chapter, bases and dimension from Volume 7, Chapter 2, and fields from Volume 6, Chapter 3.

### Definitions

**Definition (Degree).** Let $L/K$ be an extension. The degree $[L:K]$ is the dimension of $L$ as a vector space over $K$. The extension is finite if $[L:K] < \infty$, and infinite otherwise. An extension of degree $2$ is quadratic, and one of degree $3$ is cubic.

For an intermediate field $E$ of $L/K$, write $[E:K]$ for the degree of $E$ over $K$ and $[L:E]$ for the degree of $L$ over $E$.

::: mathlib
`Module.finrank` · `Mathlib.LinearAlgebra.Dimension.Finrank`

The degree is `Module.finrank K L : ℕ`. It is a natural number, so it cannot be $\infty$. When `L` has infinite dimension over `K`, Mathlib sets `Module.finrank K L = 0` (`Module.finrank_of_not_finite`). This is a junk value. The true dimension, a cardinal, is `Module.rank K L`. A finite extension is `[FiniteDimensional K L]`, which is the class `Module.Finite K L`. So a lemma about `finrank` either has a hypothesis `FiniteDimensional`, or it holds also with the value $0$.

<?decl Module.finrank?>
:::

### Theorems and proofs

**Theorem (Tower law).** Let $K \subseteq L \subseteq M$ be fields. Let $(\alpha_i)_{i \in I}$ be a basis of $L$ over $K$ and $(\beta_j)_{j \in J}$ a basis of $M$ over $L$. Then $(\alpha_i\beta_j)_{(i,j) \in I \times J}$ is a basis of $M$ over $K$. In particular $M/K$ is finite if and only if $M/L$ and $L/K$ are finite, and then $[M:K] = [M:L]\,[L:K]$.

*Proof.* First the family spans. Let $\gamma \in M$. Since $(\beta_j)$ spans $M$ over $L$, there are $b_j \in L$, almost all zero, with $\gamma = \sum_j b_j \beta_j$. Each $b_j$ lies in $L$, so there are $a_{ij} \in K$, almost all zero, with $b_j = \sum_i a_{ij}\alpha_i$. Then
$$\gamma = \sum_j \Bigl(\sum_i a_{ij}\alpha_i\Bigr)\beta_j = \sum_{i,j} a_{ij}\,\alpha_i\beta_j.$$
So $\gamma$ is a $K$-linear combination of the $\alpha_i\beta_j$.

Next the family is linearly independent. Let $a_{ij} \in K$, almost all zero, with $\sum_{i,j} a_{ij}\alpha_i\beta_j = 0$. Group the terms by $j$: $\sum_j c_j \beta_j = 0$ with $c_j = \sum_i a_{ij}\alpha_i \in L$. The $\beta_j$ are independent over $L$, so $c_j = 0$ for each $j$. The $\alpha_i$ are independent over $K$, so $a_{ij} = 0$ for each $i$ and $j$.

Thus $(\alpha_i\beta_j)$ is a basis, and $[M:K] = |I \times J| = |I|\,|J|$ as cardinals. If $L/K$ and $M/L$ are finite, the product is finite. If $M/K$ is finite, then $L$ is a $K$-subspace of $M$, so $L/K$ is finite. Also a $K$-basis of $M$ spans $M$ over $L$, since $K \subseteq L$. So $M/L$ is finite. $\square$

The proof does not use that $M$ is a field: it works for each $L$-vector space $M$. Volume 7, Chapter 2 proves the same statement for modules over rings, with free modules.

::: mathlib
`Module.finrank_mul_finrank` · `Mathlib.LinearAlgebra.Dimension.Free`

The statement is `finrank F K * finrank K A = finrank F A`, for a tower `F → K → A` with `[IsScalarTower F K A]` and free modules. Over fields each module is free, so the hypotheses hold automatically. The lemma needs no finiteness, because the junk value makes both sides $0$ when a step is infinite. The basis of the proof is `Module.Basis.smulTower`.

<?decl Module.finrank_mul_finrank?>
:::

::: mathlib
`FiniteDimensional.right` · `Mathlib.FieldTheory.Tower`

For a tower `F → K → A` with `[Module.Finite F A]`, the conclusion is `Module.Finite K A`. The lemma `FiniteDimensional.left` gives the other half, `Module.Finite F K`. These are the last two sentences of the proof above. Use them when an instance argument asks for finiteness of one step: `haveI := FiniteDimensional.right F K A`. The form `Module.Finite.right` states the same fact.

<?decl FiniteDimensional.right?>
:::

**Corollary (Degrees of intermediate fields).** Let $L/K$ be finite and $E$ an intermediate field. Then $[E:K]$ and $[L:E]$ divide $[L:K]$. If $E \subseteq F$ are intermediate fields, then $[E:K]$ divides $[F:K]$.

*Proof.* By the tower law $[L:K] = [L:E]\,[E:K]$, and both factors are finite. For $E \subseteq F$, apply the tower law to $K \subseteq E \subseteq F$. $\square$

::: mathlib
`IntermediateField.finrank_dvd_of_le_right` · `Mathlib.FieldTheory.IntermediateField.Algebraic`

The statement is `F ≤ E → finrank K F ∣ finrank K E`. It has no finiteness hypothesis. If `E` is infinite over `K`, the right side is $0$, and every number divides $0$. The companion `IntermediateField.finrank_dvd_of_le_left` gives `finrank E L ∣ finrank F L`. The inequality `IntermediateField.finrank_le_of_le_right` does need `[FiniteDimensional K E]`, as the second example shows.

<?decl IntermediateField.finrank_dvd_of_le_right?>
:::

**Corollary (Degree one).** Let $L/K$ be an extension. Then $[L:K] = 1$ if and only if $L = K$.

*Proof.* If $L = K$, then $\{1\}$ is a basis. If $[L:K] = 1$, then $\{1\}$ is a basis, since $1 \neq 0$ in a space of dimension $1$. So each $x \in L$ is $a \cdot 1$ with $a \in K$, and $L = K$. $\square$

**Corollary (Prime degree).** Let $L/K$ have prime degree $p$. Then the only intermediate fields are $K$ and $L$.

*Proof.* Let $E$ be an intermediate field. Then $[E:K]$ divides $p$, so it is $1$ or $p$. If $[E:K] = 1$, then $E = K$. If $[E:K] = p$, then $[L:E] = 1$ by the tower law, so $E = L$. $\square$

In Mathlib the first corollary is `IntermediateField.finrank_eq_one_iff : finrank F K = 1 ↔ K = ⊥`, and the second is `IntermediateField.isSimpleOrder_of_finrank_prime`. Both live in the module of Chapter 2, Section 2.

**Corollary (Degree and strict inclusion).** Let $L/K$ be finite and $E \subsetneq F$ intermediate fields. Then $[E:K] < [F:K]$ and $[L:F] < [L:E]$.

*Proof.* The tower law gives $[F:K] = [F:E]\,[E:K]$. Since $E \neq F$, the first corollary gives $[F:E] \geq 2$. The second inequality follows from $[L:E] = [L:F]\,[F:E]$. $\square$

**Theorem (Size of a finite field).** Let $L/K$ be finite of degree $n$ and $K$ finite with $q$ elements. Then $L$ has $q^n$ elements.

*Proof.* A basis $\alpha_1, \dots, \alpha_n$ gives a bijection $K^n \to L$, $(a_i) \mapsto \sum a_i\alpha_i$. $\square$

With $K = \mathbb{F}_p$, the prime field of Section 1, each finite field has $p^n$ elements. Chapter 7 studies finite fields in full. In Mathlib the theorem is `Module.card_eq_pow_finrank`.

**Definition (Relative degree).** Let $A$ and $B$ be intermediate fields of $L/K$. The relative degree of $B$ over $A$ is $[B : A \cap B]$, the degree of $B$ over the intermediate field $A \sqcap B$.

When $A \subseteq B$, this is $[B:A]$. The point of the definition is that it stays inside the lattice of intermediate fields of $L/K$: both arguments have the same type. The tower law takes the form: for $A \subseteq B \subseteq C$, the relative degrees multiply.

::: mathlib
`IntermediateField.relfinrank` · `Mathlib.FieldTheory.Relrank`

For `A B : IntermediateField F E`, `A.relfinrank B : ℕ` is the degree of `B` over `A ⊓ B`, with the junk value $0$ for infinite degree. The cardinal version is `IntermediateField.relrank`. Basic values: `IntermediateField.relfinrank_bot_left` gives `⊥.relfinrank A = finrank F A`, `IntermediateField.relfinrank_top_left` gives `⊤.relfinrank A = 1`, and `IntermediateField.relfinrank_eq_one_iff` says `A.relfinrank B = 1 ↔ B ≤ A`. Without the definition, the degree of `B` over `A` needs `B` seen as an `IntermediateField A E` with `extendScalars`, which changes the type.

<?decl IntermediateField.relfinrank?>
:::

::: mathlib
`IntermediateField.relfinrank_mul_relfinrank` · `Mathlib.FieldTheory.Relrank`

The statement is `A ≤ B → B ≤ C → A.relfinrank B * B.relfinrank C = A.relfinrank C`. This is the tower law inside one lattice. With `A = ⊥` it gives `IntermediateField.finrank_bot_mul_relfinrank`: `finrank F A * A.relfinrank B = finrank F B`.

<?decl IntermediateField.relfinrank_mul_relfinrank?>
:::

### Examples

**Example (The degree of $\mathbb{Q}(\sqrt 2, \sqrt 3)$).** Section 1 shows that $\sqrt 3 \notin \mathbb{Q}(\sqrt 2)$ and that $1, \sqrt 2$ span $\mathbb{Q}(\sqrt 2)$. They are independent, since $\sqrt 2 \notin \mathbb{Q}$. So $[\mathbb{Q}(\sqrt 2):\mathbb{Q}] = 2$. In the same way $1, \sqrt 3$ is a basis of $\mathbb{Q}(\sqrt 2, \sqrt 3)$ over $\mathbb{Q}(\sqrt 2)$, so this degree is $2$. The tower law gives
$$[\mathbb{Q}(\sqrt 2, \sqrt 3):\mathbb{Q}] = 2 \cdot 2 = 4,$$
and the product basis is $1, \sqrt 2, \sqrt 3, \sqrt 6$. This matches the description of the field in Section 1. The field $\mathbb{Q}(\sqrt 6)$ is a third quadratic intermediate field. Each intermediate field has degree $1$, $2$ or $4$.

**Example (The inequality needs finiteness).** Take $L = \mathbb{R}$ and $K = \mathbb{Q}$. The field $\mathbb{R}$ is uncountable. A vector space of finite dimension $n$ over $\mathbb{Q}$ is in bijection with $\mathbb{Q}^n$, which is countable. So $\mathbb{R}/\mathbb{Q}$ is infinite, and Mathlib gives `finrank ℚ ℝ = 0`. Now $E = \mathbb{Q}(\sqrt 2) \subseteq \mathbb{R}$ has `finrank ℚ E = 2`. So $E \leq \top$ but `finrank ℚ E = 2 > 0 = finrank ℚ ℝ`. The inequality $[E:K] \leq [L:K]$ fails for the junk value, and `IntermediateField.finrank_le_of_le_right` needs its hypothesis `[FiniteDimensional K E]`. The divisibility $2 \mid 0$ still holds, which is why `finrank_dvd_of_le_right` has no hypothesis.

**Example (A cube root and a square root).** Let $c = \sqrt[3]{2} \in \mathbb{R}$. Chapter 2 proves that $[\mathbb{Q}(c):\mathbb{Q}] = 3$, with the basis $1, c, c^2$. Suppose $\sqrt 2 \in \mathbb{Q}(c)$. Then $\mathbb{Q}(\sqrt 2)$ is an intermediate field of $\mathbb{Q}(c)/\mathbb{Q}$, and $2$ divides $3$, a contradiction. So $\sqrt 2 \notin \mathbb{Q}(c)$. Also $\mathbb{Q}(c)$ has prime degree, so its only subfields are $\mathbb{Q}$ and $\mathbb{Q}(c)$.

**Example (The complex numbers).** The numbers $1, i$ form a basis of $\mathbb{C}$ over $\mathbb{R}$, so $[\mathbb{C}:\mathbb{R}] = 2$. In Mathlib this is `Complex.finrank_real_complex`. By the prime degree corollary, no field lies strictly between $\mathbb{R}$ and $\mathbb{C}$.

### The library around it

Instances carry the finiteness in Mathlib. If `[FiniteDimensional K L]` holds, then `IntermediateField.finiteDimensional_left` gives `FiniteDimensional K E` and `IntermediateField.finiteDimensional_right` gives `FiniteDimensional E L` for each intermediate field `E`. So in a finite extension, `finrank` of an intermediate field is the true degree with no extra work. `IntermediateField.finrank_lt_of_gt` is the strict inequality of the last corollary. `IsNoetherian.iff_fg` shows that the Noetherian condition in `FiniteDimensional.left` is finiteness again.

**Common errors.** `finrank K L = 0` can mean that $L/K$ is infinite. `Module.finrank_mul_finrank` needs `IsScalarTower K L M` for three types, and it writes the lower step first.

### Exercises

1. (A) Compute $[\mathbb{Q}(\sqrt 5, i):\mathbb{Q}]$ and give a basis. Hint: $\mathbb{Q}(\sqrt 5) \subseteq \mathbb{R}$ does not contain $i$.

2. (A) Let $[L:K]$ be prime and $\alpha \in L \setminus K$. Show that $L = K(\alpha)$. Hint: the prime degree corollary.

3. (A) Let $L/K$ be finite and $E$ an intermediate field with $[L:E] = [L:K]$. Show that $E = K$. Hint: the tower law gives $[E:K] = 1$.

4. (B) Let $L/K$ be finite and $E, F$ intermediate fields of coprime degrees $m$ and $n$ over $K$. Show that $mn$ divides $[EF:K]$ and that $E \cap F = K$. Hint: both $m$ and $n$ divide $[EF:K]$, and $[E \cap F:K]$ divides $m$ and $n$.

5. (B) Show that $[EF:K] \leq [E:K]\,[F:K]$ when both are finite. Hint: show that the products $e_i f_j$ of the two bases span the ring $E[F]$, and that this ring is a field because it has finite dimension over $E$ and no zero divisors.

6. (B) Show that $\mathbb{Q}(\sqrt 2) \not\cong \mathbb{Q}(\sqrt 3)$ as fields, although both have degree $2$. Hint: an isomorphism fixes $\mathbb{Q}$, so it sends $\sqrt 2$ to a square root of $2$ in $\mathbb{Q}(\sqrt 3)$.

7. (B) A field $F$ has $2^6$ elements. Find the possible sizes of its subfields. Hint: $2^6 = (2^d)^{6/d}$, so $d$ divides $6$. Chapter 7 shows that each size occurs.

8. (C) Let $M/K$ be an extension and $L$ an intermediate field. Show that $\operatorname{rank}_K M = \operatorname{rank}_L M \cdot \operatorname{rank}_K L$ as cardinals, also when the degrees are infinite. Deduce that $[\mathbb{R}:\mathbb{Q}]$ is the cardinal of $\mathbb{R}$. Hint: the product basis. A vector space of infinite rank $\kappa$ over a countable field has exactly $\kappa$ elements.

### Notes and history

Dedekind already treated a field of algebraic numbers as a vector space over $\mathbb{Q}$. Steinitz used it in his abstract theory of 1910. Artin made linear algebra the main tool of Galois theory in his lectures, published as "Galois Theory" in 1942. The tower law is the first instance of that approach.

### Reference

<?reference?>
