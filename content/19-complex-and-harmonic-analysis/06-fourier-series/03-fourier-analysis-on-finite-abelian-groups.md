---
title: Fourier analysis on finite abelian groups
kind: theory
modules:
  - Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
  - Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
  - Mathlib.Analysis.Fourier.ZMod
explains:
  E3: [AddChar.wInner_cWeight_eq_boole, AddChar.card_eq, AddChar.sum_apply_eq_ite, AddChar.doubleDualEquiv, ZMod.dft]
  E2: [AddChar.expect_eq_ite, AddChar.wInner_cWeight_self, AddChar.linearIndependent, AddChar.card_addChar_le, AddChar.exists_apply_ne_zero, AddChar.doubleDualEmb_bijective, AddChar.complexBasis, AddChar.zmod, AddChar.zmod_intCast, AddChar.zmodAddEquiv, ZMod.dft_apply, ZMod.invDFT_apply, ZMod.dft_dft, ZMod.dft_apply_zero, ZMod.dft_eq_fourier, DirichletCharacter.fourierTransform_eq_gaussSum_mulShift]
  E1: auto
families: []
requires: [V07.C07, V16.C06, V19.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Fourier analysis on finite abelian groups

### Overview

The circle of Sections 1 and 2 is a compact abelian group, and its characters $e_n$ gave the Fourier series. The same construction works on every finite abelian group $G$. Here all integrals are finite sums, and no question of convergence arises. A new feature becomes visible: the characters of $G$ form a group $\hat G$ of the same size, and the characters of $\hat G$ give back $G$. This is Pontryagin duality in its simplest case. For the cyclic group $\mathbb{Z}/N\mathbb{Z}$ the transform is the discrete Fourier transform of numerical analysis.

Two normalisations occur. For orthogonality this section uses the mean $\mathbb{E}_{x \in G}\, h(x) = \frac{1}{|G|}\sum_{x \in G} h(x)$, as Mathlib does. For the discrete Fourier transform Mathlib uses the plain sum, with no factor, and puts $\frac1N$ in the inverse.

### Definitions

**Definition (Character).** Let $G$ be a finite abelian group, written additively. A *character* of $G$ is a map $\psi : G \to \mathbb{C}$ with $\psi(0) = 1$ and $\psi(x + y) = \psi(x)\psi(y)$. The characters form a group $\hat G$ under pointwise multiplication, the *dual group*. Its identity is the trivial character $1$.

If $|G| = m$, then $mx = 0$, so $\psi(x)^m = \psi(mx) = 1$. So every value $\psi(x)$ is a root of unity, $|\psi(x)| = 1$ and $\overline{\psi(x)} = \psi(x)^{-1} = \psi(-x)$.

**Definition (Inner product and transform).** For $f, g : G \to \mathbb{C}$ put
$$\langle f, g\rangle = \mathbb{E}_{x \in G}\,\overline{f(x)}\,g(x).$$
The *Fourier transform* of $f$ is the function $\hat f : \hat G \to \mathbb{C}$ with $\hat f(\psi) = \sum_{x \in G}\overline{\psi(x)}\,f(x)$.

::: mathlib
`AddChar.wInner_cWeight_eq_boole` · `Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality`

A character is an `AddChar G R`: a map from an additive monoid to a multiplicative one with `map_zero_eq_one` and `map_add_eq_mul`. The group `AddChar G R` is written additively, so the trivial character is `0`. The notation `⟪f, g⟫ₙ_[R]` is the inner product with the mean, the "compact" weight `cWeight`. The theorem `wInner_cWeight_eq_boole` states `⟪ψ₁, ψ₂⟫ₙ_[R] = if ψ₁ = ψ₂ then 1 else 0`.

<?decl AddChar.wInner_cWeight_eq_boole?>
<?decl AddChar.wInner_cWeight_self?>
:::

### Theorems and proofs

**Theorem (Orthogonality of characters).** (a) For $\psi \in \hat G$, $\mathbb{E}_x\,\psi(x)$ is $1$ if $\psi = 1$ and $0$ otherwise. (b) For $\psi_1, \psi_2 \in \hat G$, $\langle \psi_1, \psi_2\rangle$ is $1$ if $\psi_1 = \psi_2$ and $0$ otherwise. (c) The characters are linearly independent, and $|\hat G| \le |G|$.

*Proof.* (a) If $\psi = 1$, the mean of $1$ is $1$. If $\psi \ne 1$, choose $a$ with $\psi(a) \ne 1$, and put $S = \sum_x \psi(x)$. The map $x \mapsto a + x$ is a bijection of $G$, so
$$S = \sum_{x}\psi(a + x) = \psi(a)\sum_x\psi(x) = \psi(a) S.$$
Then $(1 - \psi(a)) S = 0$ and $S = 0$.

(b) $\overline{\psi_1(x)}\psi_2(x) = \psi_1(x)^{-1}\psi_2(x) = (\psi_1^{-1}\psi_2)(x)$. The character $\psi_1^{-1}\psi_2$ is trivial if and only if $\psi_1 = \psi_2$. Apply (a).

(c) Let $\sum_\psi c_\psi \psi = 0$ with finitely many $\psi$. Take the inner product with $\psi_0$. By (b) the result is $c_{\psi_0} = 0$. So the characters are linearly independent in the space of functions $G \to \mathbb{C}$, which has dimension $|G|$. $\square$

::: mathlib
`AddChar.expect_eq_ite` · `Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality`

Part (a) is `expect_eq_ite`: `𝔼 a, ψ a = if ψ = 0 then 1 else 0`. Part (c) is `AddChar.linearIndependent` and `card_addChar_le`.

<?decl AddChar.expect_eq_ite?>
<?decl AddChar.linearIndependent?>
<?decl AddChar.card_addChar_le?>
:::

**Theorem (Size of the dual and the dual orthogonality).** (a) $|\hat G| = |G|$. (b) For every $a \ne 0$ in $G$ there is a character $\psi$ with $\psi(a) \ne 1$. (c) For $a \in G$, $\sum_{\psi \in \hat G}\psi(a)$ is $|G|$ if $a = 0$ and $0$ otherwise.

*Proof.* For $G = \mathbb{Z}/N\mathbb{Z}$, put $\psi_k(j) = e^{2\pi i jk/N}$ for $k \in \mathbb{Z}/N\mathbb{Z}$. It is well defined and a character. A character $\psi$ is fixed by $\psi(1)$, an $N$-th root of unity $e^{2\pi i k/N}$, and then $\psi = \psi_k$. The $\psi_k$ are distinct, so $|\hat G| = N$. For $a \ne 0$, $\psi_1(a) = e^{2\pi i a/N} \ne 1$.

For a general $G$, the structure theorem (Volume 7, Chapter 7) gives $G \cong \mathbb{Z}/N_1 \times \cdots \times \mathbb{Z}/N_r$. A character of a product is the product of its restrictions to the factors, and every family of characters of the factors gives one of the product. So $|\hat G| = \prod_i N_i = |G|$, which is (a). If $a = (a_1, \dots, a_r) \ne 0$, some $a_i \ne 0$, and the character $x \mapsto \psi_1(x_i)$ of the $i$-th factor is not $1$ at $a$, which is (b).

(c) For $a = 0$ the sum is $|\hat G| = |G|$. For $a \ne 0$, take $\psi_0$ as in (b), and put $S = \sum_\psi \psi(a)$. Multiplication by $\psi_0$ is a bijection of $\hat G$, so $S = \sum_\psi (\psi_0\psi)(a) = \psi_0(a) S$, and $S = 0$. $\square$

::: mathlib
`AddChar.card_eq` · `Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality`

`card_eq : Fintype.card (AddChar α ℂ) = Fintype.card α` for a finite additive commutative group `α`. Part (b) is `exists_apply_ne_zero`, in the form `(∃ ψ, ψ a ≠ 1) ↔ a ≠ 0`, and part (c) is `sum_apply_eq_ite`. For the cyclic group the file gives `AddChar.zmod n x : AddChar (ZMod n) Circle`, the formula `zmod_intCast`, and the isomorphism `zmodAddEquiv : ZMod n ≃+ AddChar (ZMod n) ℂ`.

<?decl AddChar.card_eq?>
<?decl AddChar.exists_apply_ne_zero?>
<?decl AddChar.sum_apply_eq_ite?>
<?decl AddChar.zmod?>
<?decl AddChar.zmod_intCast?>
<?decl AddChar.zmodAddEquiv?>
:::

**Theorem (Pontryagin duality).** The map $\mathrm{ev} : G \to \hat{\hat G}$, $\mathrm{ev}(a)(\psi) = \psi(a)$, is an isomorphism of groups.

*Proof.* $\mathrm{ev}(a)$ is a character of $\hat G$, since $(\psi_1\psi_2)(a) = \psi_1(a)\psi_2(a)$. The map $\mathrm{ev}$ is a homomorphism, since $\psi(a + b) = \psi(a)\psi(b)$. Its kernel is $0$ by part (b) of the last theorem. Apply part (a) twice: $|\hat{\hat G}| = |\hat G| = |G|$. An injective map between finite sets of the same size is bijective. $\square$

::: mathlib
`AddChar.doubleDualEquiv` · `Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality`

`doubleDualEquiv : α ≃+ AddChar (AddChar α ℂ) ℂ` is built from the embedding `doubleDualEmb` and `doubleDualEmb_bijective`. The map $G \cong \hat G$ is not canonical: it depends on the choice of a decomposition. Mathlib states only the canonical isomorphism with the double dual.

<?decl AddChar.doubleDualEquiv?>
<?decl AddChar.doubleDualEmb_bijective?>
:::

**Theorem (Inversion and Parseval).** For $f : G \to \mathbb{C}$,
$$f(x) = \frac{1}{|G|}\sum_{\psi \in \hat G}\hat f(\psi)\,\psi(x), \qquad \sum_{\psi}|\hat f(\psi)|^2 = |G|\sum_{x}|f(x)|^2.$$

*Proof.* Insert the definition: $\sum_\psi \hat f(\psi)\psi(x) = \sum_y f(y)\sum_\psi \overline{\psi(y)}\psi(x) = \sum_y f(y)\sum_\psi\psi(x - y)$. By the dual orthogonality the inner sum is $|G|$ for $y = x$ and $0$ otherwise. This gives the inversion. For Parseval, the $|G|$ characters are orthonormal for $\langle\cdot,\cdot\rangle$ and so form an orthonormal basis of the $|G|$-dimensional space of functions. Since $\hat f(\psi) = |G|\langle\psi, f\rangle$, Parseval in a finite-dimensional inner product space (Volume 16, Chapter 6) gives $\sum_\psi |\hat f(\psi)|^2 = |G|^2\langle f, f\rangle = |G|\sum_x |f(x)|^2$. $\square$

::: mathlib
`ZMod.dft` · `Mathlib.Analysis.Fourier.ZMod`

`ZMod.dft : (ZMod N → E) ≃ₗ[ℂ] (ZMod N → E)`, for `[NeZero N]` and a complex normed space `E`, with notation `𝓕` in the namespace `ZMod`. The formula is `dft_apply`: `dft Φ k = ∑ j, stdAddChar (-(j * k)) • Φ j`, where `ZMod.stdAddChar j = exp (2 π i j / N)`. The inverse is `invDFT_apply`: `dft.symm Ψ k = (N)⁻¹ • ∑ j, stdAddChar (j * k) • Ψ j`. The lemma `dft_eq_fourier` shows that `dft` is the general Fourier integral of Chapter 7 for the counting measure. Mathlib indexes the transform by `ZMod N` itself, through $k \mapsto \psi_k$, and not by the dual group.

<?decl ZMod.dft?>
<?decl ZMod.dft_apply?>
<?decl ZMod.invDFT_apply?>
<?decl ZMod.dft_eq_fourier?>
<?decl ZMod.stdAddChar?>
:::

### Examples

**Example (A transform of length four).** Let $N = 4$ and $\Phi = (1, 1, 0, 0)$, that is $\Phi(0) = \Phi(1) = 1$ and $\Phi(2) = \Phi(3) = 0$. With $\omega = e^{-2\pi i/4} = -i$,
$$\hat\Phi(k) = \sum_j \omega^{jk}\Phi(j) = 1 + (-i)^k,$$
so $\hat\Phi = (2, 1 - i, 0, 1 + i)$. Parseval: $4 + 2 + 0 + 2 = 8 = 4 \cdot (1 + 1)$. Inversion at $j = 0$: $\frac14(2 + (1 - i) + 0 + (1 + i)) = 1 = \Phi(0)$.

**Example (The delta and the constant).** Let $\delta_0$ be $1$ at $0$ and $0$ elsewhere. Then $\hat\delta_0(k) = 1$ for all $k$. The constant $1$ has $\hat 1(k) = \sum_j \omega^{jk}$, which is $N$ for $k = 0$ and $0$ otherwise by orthogonality. So $\hat{\hat\delta_0} = N\delta_0$. This agrees with `dft_dft`: $\mathcal{F}\mathcal{F}\Phi(j) = N\,\Phi(-j)$.

::: mathlib
`ZMod.dft_dft` · `Mathlib.Analysis.Fourier.ZMod`

`dft_dft : dft (dft Φ) = fun j ↦ N • Φ (-j)`. The value at $0$ is `dft_apply_zero : dft Φ 0 = ∑ j, Φ j`.

<?decl ZMod.dft_dft?>
<?decl ZMod.dft_apply_zero?>
:::

**Example (Gauss sums).** For a Dirichlet character $\chi$ modulo $N$, the transform at $k$ is the Gauss sum $\sum_j \chi(j)e^{-2\pi i jk/N}$.

::: mathlib
`DirichletCharacter.fourierTransform_eq_gaussSum_mulShift` · `Mathlib.Analysis.Fourier.ZMod`

`dft χ k = gaussSum χ (stdAddChar.mulShift (-k))`.

<?decl DirichletCharacter.fourierTransform_eq_gaussSum_mulShift?>
<?decl gaussSum?>
:::

### The library around it

The general results sit in `Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality` and `.PontryaginDuality`. `AddChar.complexBasis α` is the basis of characters of `α → ℂ`. The cyclic case is `Mathlib.Analysis.Fourier.ZMod`. The index of this edition has no declaration for a fast Fourier transform algorithm, or for the Pontryagin dual of an infinite locally compact group.

Common errors of a learner:

- Writing the trivial character as `1`. In `AddChar G R` the group law is written additively, so it is `0`.
- Mixing the normalisations. `⟪ψ₁, ψ₂⟫ₙ_` is a mean, `dft` is a plain sum, and `dft.symm` carries $\frac1N$.
- Forgetting the sign: `dft` uses `stdAddChar (-(j * k))`.

### Exercises

1. (A) Compute the DFT of $\Phi = (1, 0, -1, 0)$ for $N = 4$, and check Parseval.
2. (A) List the characters of $\mathbb{Z}/2 \times \mathbb{Z}/2$ and write their table of values.
3. (B) Define $(f * g)(x) = \sum_y f(y)g(x - y)$. Show that $\widehat{f * g} = \hat f\,\hat g$.
4. (B) Show that the DFT of a real even $\Phi$ is real and even. Hint: $\overline{\hat\Phi(k)} = \hat\Phi(-k)$ for real $\Phi$.
5. (B) Let $q(x) = e^{2\pi i x^2/N}$ on $\mathbb{Z}/N\mathbb{Z}$ with $N$ odd. Show that $|\sum_x q(x)|^2 = N$. Hint: expand $|\cdot|^2$ as a double sum, put $y = x + h$, and use $2$ invertible modulo $N$.
6. (C) Let $A \subseteq G$ and $f = \mathbf{1}_A$. Show that $\max_{\psi \ne 1}|\hat f(\psi)| \le \sqrt{|A|\,|G|}$, and give an $A$ for which the bound is sharp up to a constant factor.

### Notes and history

Gauss evaluated the quadratic Gauss sums in 1805 and published the result in 1811. Dirichlet introduced the characters of $(\mathbb{Z}/N\mathbb{Z})^\times$ in 1837 for his theorem on primes in arithmetic progressions. Pontryagin proved the duality theorem for locally compact abelian groups with a countable base in 1934, and van Kampen extended it in 1935. Cooley and Tukey published the fast Fourier transform in 1965.

### Reference

<?reference?>
