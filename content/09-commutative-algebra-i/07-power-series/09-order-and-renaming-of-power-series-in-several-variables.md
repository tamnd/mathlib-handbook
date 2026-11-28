---
title: Order and renaming of power series in several variables
kind: api
modules:
  - Mathlib.RingTheory.MvPowerSeries.Order
  - Mathlib.RingTheory.MvPowerSeries.LexOrder
  - Mathlib.RingTheory.MvPowerSeries.Equiv
  - Mathlib.RingTheory.MvPowerSeries.Rename
  - Mathlib.RingTheory.MvPowerSeries.Ideal
explains:
  E2: [MvPowerSeries.weightedOrder, MvPowerSeries.order, MvPowerSeries.order_mul_ge, MvPowerSeries.homogeneousComponent, MvPowerSeries.lexOrder, MvPowerSeries.lexOrder_mul, MvPowerSeries.finSuccEquiv, MvPowerSeries.toAdicCompletionAlgEquiv, MvPowerSeries.rename, MvPowerSeries.killCompl, MvPowerSeries.ker_map_of_fg]
  E1: auto
families: []
requires: [V06.C05, V09.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Order and renaming of power series in several variables

### Overview

The order of a power series $f$ in one variable is the smallest $n$ with a nonzero coefficient of $X^n$. In several variables there is more than one choice. The total degree of a monomial $X^d = X_1^{d_1} \cdots X_k^{d_k}$ is $d_1 + \cdots + d_k$, and the order of $f$ is the smallest total degree of a monomial in $f$. A weight $w$ on the variables gives the weighted degree $\sum_i w_i d_i$ and the weighted order. A linear order on the variables gives the lexicographic order on monomials, and the lexicographic order of $f$ is its smallest monomial in that order. Each of these orders is a value in $\mathbb{N} \cup \{\infty\}$ or in the monomials with a top element, and the value $\infty$ marks the zero series.

The second theme of this section is a change of variables. A map $f : \sigma \to \tau$ between sets of variables sends $X_s$ to $X_{f(s)}$, and this extends to power series when each fiber of $f$ is finite. The library also has the equivalences that remove one variable at a time, so that $R[[X_0, \ldots, X_n]]$ becomes $R[[X_1, \ldots, X_n]][[X_0]]$, and the isomorphism between $R[[X_1, \ldots, X_n]]$ and the completion of $R[X_1, \ldots, X_n]$ at the ideal of the variables. This section is a guide to these five modules.

### The library around it

**Weighted order and order.** The module `Mathlib.RingTheory.MvPowerSeries.Order` defines `MvPowerSeries.weightedOrder w f` for a weight $w : \sigma \to \mathbb{N}$, a value in `ℕ∞`. The coefficients below the weighted order vanish, `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`, and the order is $\top$ exactly for the zero series, `MvPowerSeries.weightedOrder_eq_top_iff`. The function `MvPowerSeries.order f` is the case of the weight $1$ on every variable, so it uses the total degree, `Finsupp.degree`. The rules are those of a valuation, with an inequality for products:
$$\operatorname{ord}(f g) \ge \operatorname{ord}(f) + \operatorname{ord}(g),$$
which is `MvPowerSeries.order_mul_ge`, with the weighted form `MvPowerSeries.le_weightedOrder_mul`. For sums, $\operatorname{ord}(f + g) \ge \min(\operatorname{ord} f, \operatorname{ord} g)$, `MvPowerSeries.min_order_le_add`, with equality when the orders differ, `MvPowerSeries.order_add_of_order_ne`. There are versions for powers and finite products, `MvPowerSeries.le_order_pow` and `MvPowerSeries.le_order_prod`. The order is at least $1$ exactly when the constant coefficient is $0$, `MvPowerSeries.one_le_order_iff_constCoeff_eq_zero`, and then $\operatorname{ord}(f^n) \ge n$, `MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero`. A nonzero series has a coefficient of exactly its order, `MvPowerSeries.exists_coeff_ne_zero_and_order`. The inequality for products is not an equality in general, because the lowest parts of $f$ and $g$ can multiply to zero when $R$ has zero divisors.

**Homogeneous components.** The same module defines `MvPowerSeries.homogeneousComponent p`, the linear map that keeps the monomials of total degree $p$, and the weighted version `MvPowerSeries.weightedHomogeneousComponent`. A series is homogeneous of degree $p$, `MvPowerSeries.IsHomogeneous`, when it equals its component of degree $p$, `MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent`. Components below the order are zero, `MvPowerSeries.homogeneousComponent_of_lt_order_eq_zero`, and the component of degree equal to the order is the initial form of $f$. If $p \le \operatorname{ord} f$ and $q \le \operatorname{ord} g$, then the component of degree $p + q$ of $f g$ is the product of the components, `MvPowerSeries.homogeneousComponent_mul_of_le_order`. The lemma `MvPowerSeries.coeff_mul_prod_one_sub_of_lt_order` says that multiplication by factors $1 - g_i$ with large order does not change low coefficients. It is a tool for computations with inverses.

**The lexicographic order.** The module `Mathlib.RingTheory.MvPowerSeries.LexOrder` assumes a linear order on $\sigma$ with `WellFoundedGT σ`, for example $\sigma = \operatorname{Fin} n$. Then `MvPowerSeries.lexOrder f` is the smallest exponent of $f$ in the lexicographic order, a value in `WithTop (Lex (σ →₀ ℕ))`. It is $\top$ exactly for $f = 0$, `MvPowerSeries.lexOrder_eq_top_iff_eq_zero`. The coefficient at the lexicographic order is nonzero, `MvPowerSeries.coeff_ne_zero_of_lexOrder`. If the orders of $\varphi$ and $\psi$ are $p$ and $q$, then the coefficient of $\varphi \psi$ at $p + q$ is the product of the two leading coefficients, `MvPowerSeries.coeff_mul_of_add_lexOrder`. Over a ring with no zero divisors this gives an equality:
$$\operatorname{lex}(\varphi \psi) = \operatorname{lex}(\varphi) + \operatorname{lex}(\psi),$$
which is `MvPowerSeries.lexOrder_mul`. This is the step in the proof of Section 2 that a power series ring over a domain is a domain.

**Equivalences.** The module `Mathlib.RingTheory.MvPowerSeries.Equiv` gives the algebra isomorphisms that move one variable outside:
$$R[[X_0, \ldots, X_n]] \cong R[[X_1, \ldots, X_n]][[X_0]],$$
which is `MvPowerSeries.finSuccEquiv R n`, and the version `MvPowerSeries.optionEquivLeft σ R` for the variables indexed by `Option σ`. The variable $X_0$ goes to $X$ and $X_{j+1}$ goes to a constant, `MvPowerSeries.finSuccEquiv_X_zero` and `MvPowerSeries.finSuccEquiv_X_succ`. The coefficients are computed by `MvPowerSeries.coeff_coeff_finSuccEquiv`. With no variables the ring is $R$ itself, `MvPowerSeries.isEmptyEquiv`. The module also proves that power series in finitely many variables form the adic completion of the polynomial ring at the ideal of the variables:
$$R[[X_1, \ldots, X_n]] \cong \varprojlim_m R[X_1, \ldots, X_n] / (X_1, \ldots, X_n)^m,$$
which is `MvPowerSeries.toAdicCompletionAlgEquiv`. The map to the completion sends $p$ to its truncations, `MvPowerSeries.toAdicCompletion_apply_eq_mk_truncTotal`, with the truncation `MvPowerSeries.truncTotal` of Section 7. The key fact is that truncation is multiplicative modulo $(X_1, \ldots, X_n)^m$, `MvPowerSeries.truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars`. The Noetherian property of Section 2 is the instance `MvPowerSeries.isNoetherianRing` in this module. For a single variable $i$, `PowerSeries.toMvPowerSeries i` embeds $R[[X]]$ into $R[[X_\sigma]]$, and `PowerSeries.toMvPowerSeries_eq_subst` writes it as a substitution.

**Renaming of variables.** The module `Mathlib.RingTheory.MvPowerSeries.Rename` defines `MvPowerSeries.rename f` for a map $f : \sigma \to \tau$ with `Filter.TendstoCofinite f`, which says that the preimage of a finite set is finite. Under this hypothesis each monomial of the image comes from finitely many monomials, and `MvPowerSeries.coeff_rename` gives the coefficient as a finite sum. The map is an algebra homomorphism that sends $X_s$ to $X_{f(s)}$, `MvPowerSeries.rename_X`, and it is the substitution of the family $X_{f(s)}$ of Section 6, `MvPowerSeries.rename_eq_subst`. It respects composition, `MvPowerSeries.rename_rename`, and for an embedding $e$ it is injective, `MvPowerSeries.rename_injective`. A bijection gives an isomorphism, `MvPowerSeries.renameEquiv`. In the other direction, `MvPowerSeries.killCompl e` sets to zero the variables outside the image of an embedding $e$. It is a left inverse of the renaming, `MvPowerSeries.killCompl_comp_rename`.

**Extended ideals.** The module `Mathlib.RingTheory.MvPowerSeries.Ideal` compares an ideal $I$ of $R$ with its extension $I R[[X_\sigma]]$. If $I$ is finitely generated, then a series lies in the extension exactly when all its coefficients lie in $I$, `MvPowerSeries.mem_map_C_iff_of_fg`. For polynomials this holds for every $I$, but for power series an infinite series can need infinitely many generators. As a consequence, for a ring homomorphism $f$ with a finitely generated kernel, the kernel of the coefficientwise map is the extension of the kernel of $f$, `MvPowerSeries.ker_map_of_fg`.

#### Common errors

1. `MvPowerSeries.order_mul_ge` is an inequality. The equality $\operatorname{ord}(fg) = \operatorname{ord}(f) + \operatorname{ord}(g)$ needs that the product of the initial forms is nonzero, and the library does not state it as a general lemma. Over a domain the lexicographic order of `MvPowerSeries.lexOrder_mul` is additive.
2. `MvPowerSeries.rename f` needs the instance `Filter.TendstoCofinite f`. A constant map from an infinite set does not satisfy it, because $\sum_s X_s \mapsto \sum_s X_t$ would need an infinite sum of equal monomials.
3. The isomorphism `MvPowerSeries.toAdicCompletionAlgEquiv` needs `[Finite σ]`. The library does not state it for infinitely many variables, so a proof in that case must use other tools.

### Exercises

1. (A) Compute `MvPowerSeries.order` of $X_1^2 + X_1 X_2^3$ and of $X_1 X_2 - X_2^5$ in $\mathbb{Z}[[X_1, X_2]]$, and the order of their product.
2. (A) Give two series $f, g$ over $\mathbb{Z}/4$ in two variables with $\operatorname{ord}(fg) > \operatorname{ord}(f) + \operatorname{ord}(g)$.
3. (B) Prove from `MvPowerSeries.one_le_order_iff_constCoeff_eq_zero` and `MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero` that the coefficient of $X^d$ in $f^n$ is zero when $f$ has constant coefficient $0$ and $n$ is larger than the total degree of $d$.
4. (B) Describe the image of $X_0 X_1 + X_1^2$ under `MvPowerSeries.finSuccEquiv` for $n = 1$, as a power series in $X$ with coefficients in $R[[X_1]]$.
5. (B) Let $e : \operatorname{Fin} 2 \to \operatorname{Fin} 3$ be the inclusion. Compute `MvPowerSeries.killCompl` of $X_0 + X_1 X_2 + X_2^2$ for this embedding.
6. (C) Use `MvPowerSeries.lexOrder_mul` to prove that $R[[X_1, \ldots, X_n]]$ has no zero divisors when $R$ has none.

### Reference

<?reference?>
