---
title: Trivial square-zero extensions
kind: api
modules:
  - Mathlib.Algebra.TrivSqZeroExt.Basic
  - Mathlib.Algebra.TrivSqZeroExt.Ideal
explains:
  E2: [TrivSqZeroExt.snd_mul, TrivSqZeroExt.inr_mul_inr, TrivSqZeroExt.snd_pow_of_smul_comm, TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.mul_inv_cancel, TrivSqZeroExt.liftEquivOfComm, TrivSqZeroExt.algHom_ext, TrivSqZeroExt.kerIdeal_sq]
  E1: auto
families: []
requires: [V06.C01, V06.C02, V06.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Trivial square-zero extensions

### Overview

Let $R$ be a ring and let $M$ be an $R$-bimodule: an abelian group with a left and a right action of $R$ that commute. The trivial square-zero extension $R \oplus M$ is the product $R \times M$ with the multiplication

$$(r_1 + m_1)(r_2 + m_2) = r_1 r_2 + (r_1 m_2 + m_1 r_2).$$

The product of two elements of $M$ is zero, so $M$ becomes an ideal whose square is $0$. Mathlib writes this ring as `TrivSqZeroExt R M`, with the local notation `tsze R M`. For $M = R$ it gives the dual numbers $R[\varepsilon]$ with $\varepsilon^2 = 0$, which the library calls `DualNumber R`.

The construction is a basic tool of algebra. A map $a \mapsto a + D(a)$ from a commutative ring to its extension by $M$ is a ring homomorphism exactly when $D$ is a derivation, so derivations, tangent vectors and first-order deformations are all ring maps into a trivial square-zero extension. The extension also gives a simple example of a ring whose units are the elements with a unit first part. This section describes the ring structure, the powers and the units, the universal property, and the ideal $M$. It uses rings and algebras from Chapter 1 and Section 1, and ideals from Chapter 2.

### The library around it

#### The type and its two parts

The module `Mathlib.Algebra.TrivSqZeroExt.Basic` defines `TrivSqZeroExt R M` as the product type `R × M`. The two projections are `TrivSqZeroExt.fst` and `TrivSqZeroExt.snd`, and the two inclusions are `TrivSqZeroExt.inl`, $r \mapsto (r, 0)$, and `TrivSqZeroExt.inr`, $m \mapsto (0, m)$. Each element is the sum of its two parts (`TrivSqZeroExt.inl_fst_add_inr_snd_eq`), and the induction principle `TrivSqZeroExt.ind` reduces a statement about all elements to the elements `inl r + inr m`. The names follow one pattern: a lemma `fst_op` or `snd_op` computes a part of an operation, and a lemma `inl_op` or `inr_op` says that an inclusion respects the operation.

The right action of $R$ on $M$ is a left action of the opposite ring $R^{\mathrm{op}}$, so the library writes $m r$ as `MulOpposite.op r • m`. The ring axioms need the two actions to commute, which is the class `SMulCommClass R Rᵐᵒᵖ M`. When $R$ is commutative and the two actions agree, the class `IsCentralScalar R M` holds, and then the extension is a commutative ring (`TrivSqZeroExt.commRing`) and an $R$-algebra (`TrivSqZeroExt.instAlgebra`).

#### The multiplication

The product is fixed by its two parts:

$$\mathrm{fst}(x_1 x_2) = \mathrm{fst}\,x_1 \cdot \mathrm{fst}\,x_2, \qquad \mathrm{snd}(x_1 x_2) = \mathrm{fst}\,x_1 \cdot \mathrm{snd}\,x_2 + \mathrm{snd}\,x_1 \cdot \mathrm{fst}\,x_2.$$

These are `TrivSqZeroExt.fst_mul` and `TrivSqZeroExt.snd_mul`. The second part is the product rule of calculus: it is the derivative of a product, with $\mathrm{snd}$ in the place of the derivative. The special cases are the four products of inclusions.

| Lean name | Statement |
|---|---|
| `TrivSqZeroExt.inr_mul_inr` | $m_1 m_2 = 0$ |
| `TrivSqZeroExt.inl_mul_inr` | $r \cdot m = r m$ as an element of $M$ |
| `TrivSqZeroExt.inr_mul_inl` | $m \cdot r = m r$ as an element of $M$ |
| `TrivSqZeroExt.inl_mul_inl` | $\mathrm{inl}\,r_1 \cdot \mathrm{inl}\,r_2 = \mathrm{inl}(r_1 r_2)$ |

The first line is the reason for the name: the first part of $\mathrm{inr}\,m_1 \cdot \mathrm{inr}\,m_2$ is $0 \cdot 0$, and the second part is $0 \cdot m_2 + m_1 \cdot 0 = 0$. The associativity of the product needs the commuting actions: the second part of $(x_1 x_2) x_3$ contains $(r_1 m_2) r_3$, and the second part of $x_1 (x_2 x_3)$ contains $r_1 (m_2 r_3)$.

The inclusions and projections are bundled. The map `TrivSqZeroExt.inlHom` is a ring homomorphism $R \to R \oplus M$, and `TrivSqZeroExt.inlAlgHom` is the same map as an algebra map. The map `TrivSqZeroExt.fstHom` is the projection as an algebra map $R \oplus M \to R$. The maps `TrivSqZeroExt.inrHom` and `TrivSqZeroExt.sndHom` are only linear, because $\mathrm{inr}$ does not preserve $1$ and $\mathrm{snd}$ does not preserve products. For a commutative $R$, the algebra map of the instance is `TrivSqZeroExt.inl` (`TrivSqZeroExt.algebraMap_eq_inl`).

#### Powers

The second part of a power is a sum by the product rule. In general it is

$$\mathrm{snd}(x^n) = \sum_{i < n} r^{i}\, m\, r^{n - 1 - i}, \qquad r = \mathrm{fst}\,x,\ m = \mathrm{snd}\,x,$$

which is `TrivSqZeroExt.snd_pow_eq_sum`. If $r m = m r$, all the terms are equal, and the sum is $n r^{n-1} m$ (`TrivSqZeroExt.snd_pow_of_smul_comm`). The proof is an induction on $n$ with `TrivSqZeroExt.snd_mul`: the step adds the term $r \cdot n r^{n-1} m + m \cdot r^n$, and the hypothesis turns it into $(n + 1) r^n m$. For the dual numbers this is the formula $(a + b\varepsilon)^n = a^n + n a^{n-1} b\,\varepsilon$, so the second part of $p(a + b\varepsilon)$ is $p'(a)\, b$ for each polynomial $p$.

#### Units and inverses

An element $x$ is a unit if and only if its first part is a unit of $R$ (`TrivSqZeroExt.isUnit_iff_isUnit_fst`). One direction holds because `TrivSqZeroExt.fstHom` is a ring homomorphism. For the other, let $r = \mathrm{fst}\,x$ have the inverse $s$, and let $m = \mathrm{snd}\,x$. Then

$$(r + m)(s - s m s) = 1 - m s + m s - m s m s = 1,$$

because $r s = 1$ and the last product lies in $M \cdot M = 0$. The product on the other side is the same computation. The equivalence `TrivSqZeroExt.invertibleEquivInvertibleFst` is the same fact for chosen inverses. An element of $M$ alone is never a unit, unless $R$ is the zero ring (`TrivSqZeroExt.isUnit_inr_iff`).

The instance `TrivSqZeroExt.instInv` defines an inverse for all elements, with $\mathrm{fst}(x^{-1}) = r^{-1}$ (`TrivSqZeroExt.fst_inv`) and $\mathrm{snd}(x^{-1}) = -r^{-1} m r^{-1}$ (`TrivSqZeroExt.snd_inv`). When $R$ is a division ring, this is a true inverse for each $x$ with $r \neq 0$ (`TrivSqZeroExt.mul_inv_cancel`), and $(x^{-1})^{-1} = x$ for such $x$ (`TrivSqZeroExt.inv_inv`). The extension is not a division ring when $M \neq 0$, because the elements of $M$ have no inverse.

#### The universal property

Let $A$ be an $R$-algebra, with $R$ commutative and $M$ an $R$-module with equal left and right actions. An algebra map $\varphi$ from $R \oplus M$ to $A$ is fixed by the linear map $f = \varphi \circ \mathrm{inr}$, because $\varphi(r + m) = r \cdot 1 + f(m)$. The map $f$ must satisfy $f(m_1) f(m_2) = \varphi(m_1 m_2) = 0$. Conversely, each linear map $f : M \to A$ with $f(m_1) f(m_2) = 0$ for all $m_1, m_2$ gives an algebra map $r + m \mapsto r \cdot 1 + f(m)$: the product

$$(r_1 + f(m_1))(r_2 + f(m_2)) = r_1 r_2 + r_1 f(m_2) + r_2 f(m_1) + f(m_1) f(m_2)$$

has a last term $0$. This is the equivalence `TrivSqZeroExt.liftEquivOfComm`. So two algebra maps that agree on $M$ are equal (`TrivSqZeroExt.algHom_ext`).

The general form works over a noncommutative $R$ that is an $S$-algebra. The map `TrivSqZeroExt.lift` takes an algebra map $g : R \to A$ and an $S$-linear map $f : M \to A$, with $f(m_1) f(m_2) = 0$, $f(r m) = g(r) f(m)$ and $f(m r) = f(m) g(r)$. The equivalence `TrivSqZeroExt.liftEquiv` bundles it, and `TrivSqZeroExt.algHom_ext'` says that an algebra map is fixed by its restrictions to $R$ and to $M$. In other words, $R \oplus M$ is generated by the images of $R$ and $M$ (`TrivSqZeroExt.range_inlAlgHom_sup_adjoin_range_inr`).

A linear map $g : M \to N$ gives the algebra map `TrivSqZeroExt.map g`, the identity on $R$ and $g$ on $M$ (`TrivSqZeroExt.map_inr`). This is functorial (`TrivSqZeroExt.map_comp_map`), so `TrivSqZeroExt R` turns $R$-modules into $R$-algebras.

#### The ideal of square zero

The module `Mathlib.Algebra.TrivSqZeroExt.Ideal` names the ideal $M$. For a commutative semiring $R$ and equal actions, `TrivSqZeroExt.kerIdeal R M` is the kernel of the projection to $R$, and an element lies in it if and only if it is $\mathrm{inr}$ of its second part (`TrivSqZeroExt.mem_kerIdeal_iff_inr`). Its square is the zero ideal (`TrivSqZeroExt.kerIdeal_sq`). The proof: the square is generated by the products $x y$ with $x, y$ in the ideal, and each such product is $\mathrm{inr}\,m_1 \cdot \mathrm{inr}\,m_2 = 0$.

This ideal is the reason for the name. An extension of $R$ by $M$ is a ring $B$ with a surjection $B \to R$ whose kernel $I$ satisfies $I^2 = 0$ and is isomorphic to $M$ as a module. The extension is *trivial* when the surjection has a section that is a ring homomorphism, and then $B$ is isomorphic to $R \oplus M$. Volume 10 uses such ideals of square zero for derivations and for formally smooth algebras.

#### Common errors

1. The right action of $R$ on $M$ is written `MulOpposite.op r • m`. A goal with `m * r` in mind needs this form, and a lemma for a commutative ring may ask for `IsCentralScalar R M` to replace it with `r • m`.
2. `TrivSqZeroExt.inr` is not a ring homomorphism, since $\mathrm{inr}(1) \neq 1$ unless $R$ is the zero ring. It is bundled only as the linear map `TrivSqZeroExt.inrHom`.
3. The formula $\mathrm{snd}(x^n) = n r^{n-1} m$ of `TrivSqZeroExt.snd_pow_of_smul_comm` needs the hypothesis $r m = m r$. Over a noncommutative $R$, the general sum `TrivSqZeroExt.snd_pow_eq_sum` is needed.

### Exercises

1. (A) Use `TrivSqZeroExt.snd_mul` to compute $(2 + 3\varepsilon)(5 - \varepsilon)$ in `TrivSqZeroExt ℤ ℤ`.
2. (A) Show that $\mathrm{inr}\,m$ is nilpotent for each $m \in M$, with `TrivSqZeroExt.inr_mul_inr`.
3. (B) Let $p$ be a polynomial over a commutative ring $R$. Show that $p(a + \varepsilon) = p(a) + p'(a)\,\varepsilon$ in `TrivSqZeroExt R R`.
4. (B) Find the inverse of $3 + 2\varepsilon$ in `TrivSqZeroExt ℚ ℚ` with `TrivSqZeroExt.snd_inv`, and check it with `TrivSqZeroExt.mul_inv_cancel`.
5. (B) Show that $R[X]/(X^2)$ is isomorphic to `TrivSqZeroExt R R` as an $R$-algebra, using `TrivSqZeroExt.liftEquivOfComm` for one direction.
6. (C) Let $R$ be a commutative ring and $D : R \to M$ an additive map. Prove that $a \mapsto \mathrm{inl}\,a + \mathrm{inr}\,D(a)$ is a ring homomorphism if and only if $D(1) = 0$ and $D(ab) = a D(b) + b D(a)$.

### Reference

<?reference?>
