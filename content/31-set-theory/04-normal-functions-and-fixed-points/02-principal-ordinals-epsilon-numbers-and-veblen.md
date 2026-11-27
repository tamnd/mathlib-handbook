---
title: Principal ordinals, epsilon numbers and the Veblen hierarchy
kind: theory
modules:
  - Mathlib.SetTheory.Ordinal.Principal
  - Mathlib.SetTheory.Ordinal.Veblen
  - Mathlib.SetTheory.Ordinal.FundamentalSequence
explains:
  E3: [Ordinal.IsPrincipal, Ordinal.isPrincipal_add_iff_zero_or_omega0_opow, Ordinal.veblen, Ordinal.epsilon, Ordinal.gamma, Ordinal.IsFundamentalSeq]
  E2: [Ordinal.not_bddAbove_setOfPred_isPrincipal, Ordinal.isPrincipal_add_iff_add_left_eq_self, Ordinal.isPrincipal_add_omega0_opow, Ordinal.add_omega0_opow, Ordinal.isPrincipal_mul_iff_le_two_or_omega0_opow_opow, Ordinal.isPrincipal_opow_iff_zero_or_two_or_omega0_or_epsilon, Ordinal.veblenWith, Ordinal.veblen_zero_apply, Ordinal.isNormal_veblen, Ordinal.veblen_veblen_of_lt, Ordinal.veblen_lt_veblen_iff_right, Ordinal.epsilon_eq_deriv, Ordinal.epsilon_zero_eq_nfp, Ordinal.mem_range_epsilon, Ordinal.lt_epsilon_zero, Ordinal.omega0_lt_epsilon, Ordinal.mem_range_gamma, Ordinal.gamma_zero_eq_nfp, Ordinal.lt_gamma_zero, Ordinal.epsilon_zero_lt_gamma, Ordinal.exists_isFundamentalSeq, Ordinal.IsFundamentalSeq.iSup_add_one_eq]
  E1: auto
families: []
requires: [V31.C02, V31.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Principal ordinals, epsilon numbers and the Veblen hierarchy

### Overview

Section 1 gave two tools: each normal function $f$ has a least fixed point $\mathrm{nfp}\,f\,a$ above each $a$, and the fixed points of $f$ are the values of a new normal function, the derivative $f'$. This section applies the tools again and again, and so builds the large countable ordinals that proof theory uses.

The first step is a question about closure. For which ordinals $o$ is the set of ordinals below $o$ closed under addition? The answer is 0 and the powers $\omega^\alpha$. The same question for multiplication gives the powers $\omega^{\omega^\alpha}$ and the ordinals at most 2. For exponentiation, it gives the fixed points of $\alpha \mapsto \omega^\alpha$, the *epsilon numbers*. The least of them is $\varepsilon_0$, met in Chapter 3 as the limit of the towers $\omega^{\omega^{\cdot^{\cdot}}}$.

The epsilon numbers are the values of the derivative of $\alpha \mapsto \omega^\alpha$. The Veblen hierarchy repeats this step transfinitely: $\varphi_0(\alpha) = \omega^\alpha$, and $\varphi_\beta$ enumerates the common fixed points of the $\varphi_\gamma$ for $\gamma < \beta$. The least ordinal $\Gamma_0$ with $\varphi_{\Gamma_0}(0) = \Gamma_0$ is the limit of this process. At the end, the section defines fundamental sequences, which name a cofinal sequence for each limit ordinal.

### Definitions

**Definition (Principal ordinal).** Let $\ast$ be a binary operation on the ordinals. An ordinal $o$ is *principal* for $\ast$ if $a \ast b < o$ for each $a < o$ and $b < o$.

Mathlib calls 0 principal for each operation, because the condition holds with no $a$. The usual books exclude 0. Mathlib makes this choice so that the statements need fewer cases. Also, 1 is principal for addition, because $0 + 0 = 0 < 1$.

**Definition (Veblen hierarchy).** Let $f$ be a normal function. The *Veblen hierarchy* starting from $f$ is the family of functions $\varphi^f_\beta$ defined by transfinite recursion on $\beta$:

- $\varphi^f_0 = f$;
- for $\beta \ne 0$, $\varphi^f_\beta$ is the derivative of the family $(\varphi^f_\gamma)_{\gamma < \beta}$, that is, the function that enumerates in increasing order the common fixed points of all $\varphi^f_\gamma$ with $\gamma < \beta$.

The *Veblen function* is $\varphi_\beta = \varphi^f_\beta$ for $f(\alpha) = \omega^\alpha$. Section 1 gives the derivative of a family of normal functions, so each $\varphi_\beta$ with $\beta \ne 0$ is normal.

**Definition (Epsilon numbers and the gamma function).** The *epsilon function* is $\varepsilon_\alpha = \varphi_1(\alpha)$, and $\varepsilon_0 = \varphi_1(0)$. The *gamma function* $\Gamma$ is the derivative of the map $\beta \mapsto \varphi_\beta(0)$, and $\Gamma_0 = \Gamma(0)$ is the *Feferman-Schütte ordinal*.

**Definition (Fundamental sequence).** Let $o$ be an ordinal and let $a = (\operatorname{cf} o).\mathrm{ord}$. A *fundamental sequence* for $o$ is a strictly increasing map $f$ from the ordinals below $a$ to the ordinals below $o$, with cofinal range.

For a countable limit ordinal $o$, $\operatorname{cf} o = \aleph_0$, so a fundamental sequence is an increasing sequence $f(0) < f(1) < \cdots$ with limit $o$. For a successor $o = b + 1$, the cofinality is 1, and the fundamental sequence is the one value $b$.

### Theorems and proofs

**Theorem (Principal ordinals are unbounded).** For each operation $\ast$ and each ordinal $a$, there is a principal ordinal $o \ge a$ for $\ast$.

*Proof.* Let $a_0 = a$ and let $a_{n+1}$ be the supremum of the values $x \ast y + 1$ for $x, y \le a_n$, and of $a_n$. This is a small family, so the supremum exists by Chapter 2. Let $o = \sup_n a_n$. If $x, y < o$, then $x, y \le a_n$ for some $n$, so $x \ast y < a_{n+1} \le o$. $\square$

**Lemma (Additive principal ordinals).** An ordinal $o$ is principal for addition if and only if $a + o = o$ for each $a < o$.

*Proof.* Assume that $o$ is principal and $a < o$. If $o = 0$ there is nothing to prove. Otherwise $o$ is 1 or a limit, because $b + 1 < o$ for each $b < o$ when $1 < o$. For a limit, $a + o = \sup_{b < o}(a + b)$ by the normality of $a + \cdot$ (Chapter 3), and each $a + b$ is below $o$. So $a + o \le o$, and $o \le a + o$ always. For $o = 1$, $a = 0$.

Conversely, assume that $a + o = o$ for each $a < o$, and let $a, b < o$. Then $a + b < a + o = o$, because $a + \cdot$ is strictly increasing. $\square$

**Theorem (Additive principal ordinals are powers of $\omega$).** An ordinal $o$ is principal for addition if and only if $o = 0$ or $o = \omega^\alpha$ for some $\alpha$.

*Proof.* First, $\omega^\alpha$ is principal. Let $a, b < \omega^\alpha$. By the Cantor normal form of Chapter 3, $a$ and $b$ are finite sums of terms $\omega^\gamma \cdot n$ with $\gamma < \alpha$. So $a, b < \omega^\gamma \cdot n$ for one $\gamma < \alpha$ and one natural number $n$. Then $a + b < \omega^\gamma \cdot 2n < \omega^\gamma \cdot \omega = \omega^{\gamma + 1} \le \omega^\alpha$.

Conversely, let $o \ne 0$ be principal, and let $\omega^\alpha$ be the leading term of its Cantor normal form, so $o = \omega^\alpha \cdot n + r$ with $n \ge 1$ and $r < \omega^\alpha$. Assume that $o \ne \omega^\alpha$. Then $\omega^\alpha < o$, and $o$ is the sum of $n$ copies of $\omega^\alpha$ and of $r$, with $r < o$. So $o$ is a finite sum of ordinals below $o$. By induction on the number of terms, a finite sum of ordinals below a principal $o$ is below $o$. This is a contradiction. $\square$

For example, $\omega \cdot 2$ is not principal, because $\omega < \omega \cdot 2$ and $\omega + \omega = \omega \cdot 2$. But $\omega^2$ is principal: $\omega \cdot n + m + \omega \cdot k + l = \omega \cdot (n + k) + l < \omega^2$.

**Theorem (Multiplicative and exponential principal ordinals).**

1. An ordinal $o$ is principal for multiplication if and only if $o \le 2$ or $o = \omega^{\omega^\alpha}$ for some $\alpha$.
2. An ordinal $o$ is principal for exponentiation if and only if $o = 0$, $o = 2$, $o = \omega$, or $o = \varepsilon_\alpha$ for some $\alpha$.

*Proof sketch of part 2.* Let $o > \omega$ be principal for exponentiation. Then $o$ is principal for multiplication, by $a \cdot b \le \max(a, b)^2$ when both are at least 2. By part 1, $o = \omega^{\omega^\beta}$. For $a < o$, $\omega^a < o$ because $\omega < o$. So $\omega^o = \sup_{a < o} \omega^a \le o$ by the normality of $\omega^\cdot$, and $o \le \omega^o$ always. So $o$ is a fixed point of $\omega^\cdot$. Conversely, let $\omega^o = o$, and let $a, b < o$. Write $a < \omega^c$ and $b < \omega^d$ with $c, d < o$. Then $a^b \le (\omega^c)^{\omega^d} = \omega^{c \cdot \omega^d}$, and $c \cdot \omega^d < o$ because $o$ is principal for multiplication. So $a^b < \omega^o = o$. $\square$

**Theorem (Epsilon numbers).** The function $\alpha \mapsto \varepsilon_\alpha$ is normal, and its range is the set of fixed points of $\alpha \mapsto \omega^\alpha$. Also $$\varepsilon_0 = \mathrm{nfp}(\omega^\cdot, 0) = \sup \{0, 1, \omega, \omega^\omega, \omega^{\omega^\omega}, \dots\},$$ and $\varepsilon_{\alpha + 1} = \mathrm{nfp}(\omega^\cdot, \varepsilon_\alpha + 1)$.

*Proof.* By the definition, $\varphi_1$ is the derivative of the single function $\varphi_0 = \omega^\cdot$. Section 1 proves that a derivative is normal and enumerates the fixed points, that its value at 0 is the least fixed point $\mathrm{nfp}\,f\,0$, and that its value at $\alpha + 1$ is the least fixed point above its value at $\alpha$. The formula for $\mathrm{nfp}$ as the supremum of the iterates is also in Section 1. $\square$

So $\varepsilon_0$ is the least $o$ with $\omega^o = o$. An ordinal $o$ is below $\varepsilon_0$ if and only if $o$ is below some finite tower $\omega^{\omega^{\cdot^{\cdot^\omega}}}$. This matches the description of $\varepsilon_0$ by the ordinal notations of Chapter 3.

**Theorem (The Veblen hierarchy).**

1. Each function $\varphi_\beta$ is normal.
2. If $\gamma < \beta$, then $\varphi_\gamma(\varphi_\beta(\alpha)) = \varphi_\beta(\alpha)$.
3. The function $\beta \mapsto \varphi_\beta(0)$ is normal.

*Proof.* (1) For $\beta = 0$, the function $\omega^\cdot$ is normal by Chapter 3. For $\beta \ne 0$, $\varphi_\beta$ is the derivative of a small family of normal functions, so it is normal by Section 1. (2) By the definition, the values of $\varphi_\beta$ are common fixed points of the $\varphi_\gamma$ for $\gamma < \beta$. (3) The function is strictly increasing: for $\gamma < \beta$, $\varphi_\gamma(0) < \varphi_\gamma(\varphi_\beta(0)) = \varphi_\beta(0)$, since $0 < \varphi_\beta(0)$. The proof of continuity at limits uses that, for a limit $\beta$, the common fixed points of the $\varphi_\gamma$ with $\gamma < \beta$ are the intersection of their ranges, and the least element of this intersection is the supremum of the values $\varphi_\gamma(0)$. $\square$

**Theorem (The Feferman-Schütte ordinal).** The gamma function is normal, and its range is the set of $o$ with $\varphi_o(0) = o$. The least such ordinal is $$\Gamma_0 = \sup \{0, \varphi_0(0), \varphi_{\varphi_0(0)}(0), \dots\},$$ and $\varepsilon_0 < \Gamma_0$.

*Proof.* The gamma function is the derivative of the normal function of part 3. The formula for $\Gamma_0$ is the formula for $\mathrm{nfp}$ from Section 1. For the bound, $\varphi_0(0) = 1$, $\varphi_1(0) = \varepsilon_0$, and the next iterate is $\varphi_{\varepsilon_0}(0) > \varepsilon_0$. $\square$

Each of $\varepsilon_0$, $\varepsilon_{\varepsilon_0}$, $\varphi_2(0)$ and $\Gamma_0$ is countable. A countable supremum of countable ordinals is countable, by the regularity of $\aleph_1$ (Chapter 6).

**Theorem (Existence of fundamental sequences).** Each ordinal has a fundamental sequence.

*Proof.* Chapter 6, Section 1 gives a cofinal subset $T$ of the ordinals below $o$ of order type $(\operatorname{cf} o).\mathrm{ord}$. The order isomorphism of the ordinals below this type with $T$ is strictly increasing with cofinal range. $\square$

### Examples

**Example (Absorption).** Because $\omega^2$ is principal for addition, $\omega \cdot 5 + 3 + \omega^2 = \omega^2$. In general, $a + \omega^\beta = \omega^\beta$ whenever $a < \omega^\beta$. This is the reason that a Cantor normal form can only have decreasing exponents: a smaller term in front of a larger power is absorbed.

**Example (A fundamental sequence for $\varepsilon_0$).** The sequence $t_0 = 0$, $t_{n+1} = \omega^{t_n}$ is strictly increasing with limit $\varepsilon_0$. So it is a fundamental sequence for $\varepsilon_0$. A fundamental sequence for $\omega^2$ is $\omega \cdot n$, and for $\omega^\omega$ it is $\omega^n$. The fast growing hierarchy that the Mathlib file on notations defines uses such sequences to turn ordinals into functions on $\mathbb{N}$.

**Example (Values of $\varphi$).** $\varphi_0(1) = \omega$, $\varphi_0(\omega) = \omega^\omega$, and $\varphi_1(0) = \varepsilon_0$. The ordinal $\varphi_2(0)$ is the least $o$ with $\varepsilon_o = o$. It is the limit of $\varepsilon_0, \varepsilon_{\varepsilon_0}, \varepsilon_{\varepsilon_{\varepsilon_0}}, \dots$.

**Counterexample (Not principal).** The ordinal $\omega + 1$ is not principal for addition: $\omega$ and $1$ are below $\omega + 1$, but their sum is $\omega + 1$ itself. The ordinal $\omega^2$ is principal for addition but not for multiplication, because $\omega \cdot \omega = \omega^2$. The ordinal $\omega^\omega$ is principal for multiplication but not for exponentiation, because $\omega^\omega$ is a value of $\omega^\cdot$ at the argument $\omega < \omega^\omega$.

### The library around it

::: mathlib
`Ordinal.IsPrincipal` · `Mathlib.SetTheory.Ordinal.Principal`

`IsPrincipal op o : Prop` is `∀ ⦃a b⦄, a < o → b < o → op a b < o`, and 0 is principal. Unboundedness is `not_bddAbove_setOfPred_isPrincipal`. For addition: `isPrincipal_add_iff_add_left_eq_self`, `isPrincipal_add_omega0_opow`, `add_omega0_opow (h : a < ω ^ b) : a + ω ^ b = ω ^ b`. The classifications are `isPrincipal_add_iff_zero_or_omega0_opow`, `isPrincipal_mul_iff_le_two_or_omega0_opow_opow` and `isPrincipal_opow_iff_zero_or_two_or_omega0_or_epsilon`.

<?decl Ordinal.isPrincipal_add_iff_zero_or_omega0_opow?>
:::

<?decl Ordinal.IsPrincipal?>

::: mathlib
`Ordinal.veblen` · `Mathlib.SetTheory.Ordinal.Veblen`

`veblenWith f o` is the hierarchy from a normal `f`, defined by `veblenWith f 0 = f` and, for `o ≠ 0`, `derivFamily` of the `veblenWith f x` with `x < o`. `veblen` is `veblenWith (ω ^ ·)`, and `veblen_zero_apply : veblen 0 a = ω ^ a`. Normality is `isNormal_veblen`, and the fixed point property is `veblen_veblen_of_lt (h : o₁ < o₂) : veblen o₁ (veblen o₂ a) = veblen o₂ a`.

<?decl Ordinal.veblen?>
:::

::: mathlib
`Ordinal.epsilon` · `Mathlib.SetTheory.Ordinal.Veblen`

`epsilon` is an abbreviation for `veblen 1`, with the scoped notations `ε_ o` and `ε₀`. The theorem is `epsilon_eq_deriv`, `epsilon_zero_eq_nfp : ε₀ = nfp (fun a ↦ ω ^ a) 0`, `mem_range_epsilon : o ∈ range epsilon ↔ ω ^ o = o` and `lt_epsilon_zero : o < ε₀ ↔ ∃ n : ℕ, o < (fun a ↦ ω ^ a)^[n] 0`.

<?decl Ordinal.epsilon?>
:::

::: mathlib
`Ordinal.gamma` · `Mathlib.SetTheory.Ordinal.Veblen`

`gamma = deriv (veblen · 0)`, with the notations `Γ_ o` and `Γ₀`. The lemmas are `mem_range_gamma : o ∈ range Γ_ ↔ veblen o 0 = o`, `gamma_zero_eq_nfp`, `lt_gamma_zero` and `epsilon_zero_lt_gamma`. The file lists as a TODO the theorem that the ordinals principal for `veblen` are the gamma ordinals and 0.

<?decl Ordinal.gamma?>
:::

::: mathlib
`Ordinal.IsFundamentalSeq` · `Mathlib.SetTheory.Ordinal.FundamentalSequence`

`IsFundamentalSeq (f : Iio a → Iio o)` has the fields `le_ord_cof : a ≤ o.cof.ord`, `strictMono` and `isCofinal_range`. The existence is `exists_isFundamentalSeq (ha : o.cof.ord = a)`, and `IsFundamentalSeq.iSup_add_one_eq` recovers `o` as the least strict upper bound. Chapter 6 uses it to prove that successor cardinals are regular.

<?decl Ordinal.IsFundamentalSeq?>
:::

Common errors:

- The notations `ε_`, `ε₀`, `Γ_` and `Γ₀` are scoped. Write `open Ordinal` first.
- `IsPrincipal` counts 0 as principal. A statement "the principal ordinals are the powers of $\omega$" from a book needs the extra case $o = 0$ in Lean.
- `ω ^ ·` in these files is ordinal exponentiation, from `Mathlib.SetTheory.Ordinal.Exponential`. Do not confuse it with the power of cardinals: `(ℵ₀ : Cardinal) ^ ℵ₀` is the continuum, but `ω ^ ω` is a countable ordinal.

### Exercises

1. (A) Decide which of $\omega \cdot 3$, $\omega^3$, $\omega^\omega + 1$ and $\omega^{\omega + 1}$ are principal for addition, and which are principal for multiplication.
2. (A) Compute $\omega^2 \cdot 3 + \omega^5$ and $\varepsilon_0 + \omega^{\varepsilon_0 + 1}$.
3. (A) Give a fundamental sequence for $\omega^\omega + \omega$, for $\varepsilon_1$ and for $\omega_1 + \omega$.
4. (B) Prove part 1 of the theorem on multiplicative principal ordinals for the powers $\omega^{\omega^\alpha}$.
5. (B) Show that $\varepsilon_\alpha$ is principal for exponentiation, and that $\omega < \varepsilon_\alpha$.
6. (B) Show that $\varphi_1(\alpha) = \varepsilon_\alpha$ and that $\varphi_2(0) = \sup_n e_n$, where $e_0 = 0$ and $e_{n+1} = \varepsilon_{e_n}$.
7. (C) Let $\alpha$ be principal for addition, with $0 < \alpha < \Gamma_0$. Show that $\alpha = \varphi_\beta(\gamma)$ for unique ordinals $\beta < \alpha$ and $\gamma < \alpha$.
8. (L) In Lean, with `open Ordinal`, prove `ω ^ ε₀ = ε₀` from `Ordinal.mem_range_epsilon`.

### Notes and history

Cantor introduced the epsilon numbers in his *Beiträge* of 1897. Veblen defined his hierarchy of normal functions in 1908. Gentzen used the ordinal $\varepsilon_0$ in his proof of the consistency of arithmetic in 1936. Feferman and Schütte, independently, identified $\Gamma_0$ in the 1960s as the limit of predicative mathematics in their sense.

### Reference

<?reference?>
