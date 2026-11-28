---
title: The modular group, congruence subgroups and cusps
kind: api
modules:
  - Mathlib.NumberTheory.Modular
  - Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
  - Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
  - Mathlib.NumberTheory.ModularForms.Cusps
  - Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
  - Mathlib.NumberTheory.HeckeRing.Defs
explains:
  E2: [ModularGroup.fd, ModularGroup.exists_smul_mem_fd, ModularGroup.cases_of_mem_fd_smul_mem_fd, Subgroup.IsArithmetic, CongruenceSubgroup.Gamma, CongruenceSubgroup.Gamma0, CongruenceSubgroup.IsCongruenceSubgroup, IsCusp, Subgroup.strictWidthInfty, IsHeckeTriple]
  E1: auto
families: []
requires: [V19.C09, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The modular group, congruence subgroups and cusps

### Overview

The modular group $\mathrm{SL}_2(\mathbb{Z})$ acts on the upper half plane $\mathbb{H}$ by Möbius transformations $z \mapsto \frac{az + b}{cz + d}$. Modular forms are functions on $\mathbb{H}$ with a transformation law under this group or under a subgroup of finite index. So before the forms, the groups: the fundamental domain of $\mathrm{SL}_2(\mathbb{Z})$, the congruence subgroups $\Gamma(N)$, $\Gamma_0(N)$ and $\Gamma_1(N)$, the arithmetic subgroups of $\mathrm{GL}_2(\mathbb{R})$, and the cusps, the points of $\mathbb{P}^1(\mathbb{R})$ where a modular form has a Fourier expansion.

The module `Mathlib.NumberTheory.Modular` constructs the fundamental domain. The modules `Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups` and `Mathlib.NumberTheory.ModularForms.CongruenceSubgroups` define the groups, and `Mathlib.NumberTheory.ModularForms.Cusps` defines cusps, periods and widths. The module `Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous` gives the instance that a discrete subgroup acts properly discontinuously on $\mathbb{H}$. The module `Mathlib.NumberTheory.HeckeRing.Defs` sets up the abstract Hecke rings. The upper half plane, the action and the generators `ModularGroup.S` and `ModularGroup.T` are in Chapter 9 of Volume 19.

### The library around it

#### The fundamental domain

Recall $S = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$ with $Sz = -1/z$, and $T = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ with $Tz = z + 1$. The standard fundamental domain is
$$\mathcal{D} = \{z \in \mathbb{H} \mid \lvert z \rvert \geq 1,\ \lvert \mathrm{Re}\,z \rvert \leq \tfrac12\},$$
the set `ModularGroup.fd`, and its interior $\mathcal{D}^\circ$, with strict inequalities, is `ModularGroup.fdo`. The library writes them with the scoped notations 𝒟 and 𝒟ᵒ.

**Theorem.** Each orbit of $\mathrm{SL}_2(\mathbb{Z})$ on $\mathbb{H}$ meets $\mathcal{D}$. If $z$ and $gz$ are both in $\mathcal{D}^\circ$, then $g = \pm 1$.

*Proof.* Since $\mathrm{Im}(gz) = \mathrm{Im}(z)/\lvert cz + d \rvert^2$ and the bottom rows $(c, d)$ are coprime pairs, only finitely many pairs make $\lvert cz + d \rvert$ small, so $\mathrm{Im}(gz)$ has a maximum over $g$ (`ModularGroup.exists_max_im`). Take $g$ with the maximum, and a power of $T$ that moves the real part into $[-\frac12, \frac12]$. If the result had $\lvert z \rvert < 1$, then $S$ would increase the imaginary part (`ModularGroup.im_lt_im_S_smul`), a contradiction. For the second part, the bound $\mathrm{Im}(z)^2 > 3/4$ on $\mathcal{D}^\circ$ forces $\lvert c \rvert \leq 1$, and the cases $c = 0$ and $c = \pm 1$ are checked by hand. $\square$

The first part is `ModularGroup.exists_smul_mem_fd`. The library proves a finer form of the second part: `ModularGroup.cases_of_mem_fd_smul_mem_fd` lists, for $z$ and $gz$ both in $\mathcal{D}$, all the possible $g$ up to sign, with the boundary conditions on $z$ for each one. The stabilizers of the corner points are `ModularGroup.stabilizer_I` for $i$, of order $4$, and `ModularGroup.stabilizer_ρ` for $\rho = e^{2\pi i/3}$, of order $6$. `ModularGroup.stabilizer_of_ne` says that each other point of $\mathcal{D}$ (other than $\rho + 1$) has stabilizer $\{\pm 1\}$. Other facts:

| Lean name | Statement |
|---|---|
| `ModularGroup.three_lt_four_mul_im_sq_of_mem_fdo` | $\mathrm{Im}(z)^2 > 3/4$ on $\mathcal{D}^\circ$ |
| `ModularGroup.abs_two_mul_re_lt_one_of_mem_fdo` | $\lvert 2\,\mathrm{Re}\,z \rvert < 1$ on $\mathcal{D}^\circ$ |
| `ModularGroup.fd_eq_closure_fdo` | $\mathcal{D}$ is the closure of $\mathcal{D}^\circ$ |
| `ModularGroup.exists_eq_T_zpow_of_c_eq_zero` | if $c = 0$, $g$ acts as a power of $T$ |
| `ModularGroup.isCompact_truncatedFundamentalDomain` | $\mathcal{D} \cap \{\mathrm{Im}\,z \leq y\}$ is compact |

#### Arithmetic subgroups

Modular forms in Mathlib are defined for a subgroup $\Gamma$ of $\mathrm{GL}_2(\mathbb{R})$. The image of $\mathrm{SL}_2(\mathbb{Z})$ is the range of `Matrix.SpecialLinearGroup.mapGL ℝ`, with the scoped notation 𝒮ℒ. A subgroup $\Gamma$ is arithmetic, `Subgroup.IsArithmetic Γ`, when it is commensurable with this image: the intersection has finite index in both. This is `Subgroup.isArithmetic_iff`. For the image of a subgroup of $\mathrm{SL}_2(\mathbb{Z})$, `Subgroup.isArithmetic_iff_finiteIndex` reduces it to finite index. The conditions `Subgroup.HasDetOne` and `Subgroup.HasDetPlusMinusOne` restrict the determinants of the elements. They are needed to multiply modular forms of different weights. `Subgroup.adjoinNegOne Γ` is the subgroup generated by $\Gamma$ and $-1$, of index at most $2$ over $\Gamma$.

#### Congruence subgroups

For $N \in \mathbb{N}$, the subgroups of $\mathrm{SL}_2(\mathbb{Z})$ are:

| Lean name | Condition on $\begin{pmatrix} a & b \\ c & d \end{pmatrix}$ modulo $N$ | Membership |
|---|---|---|
| `CongruenceSubgroup.Gamma N` | $\equiv \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}$ | `CongruenceSubgroup.Gamma_mem` |
| `CongruenceSubgroup.Gamma1 N` | $\equiv \begin{pmatrix} 1 & * \\ 0 & 1 \end{pmatrix}$ | `CongruenceSubgroup.Gamma1_mem` |
| `CongruenceSubgroup.Gamma0 N` | $c \equiv 0$ | `CongruenceSubgroup.Gamma0_mem` |

So $\Gamma(N) \leq \Gamma_1(N) \leq \Gamma_0(N)$, by `CongruenceSubgroup.Gamma_le_Gamma1` and `CongruenceSubgroup.Gamma1_le_Gamma0`. The group $\Gamma(N)$ is the kernel of the reduction to $\mathrm{SL}_2(\mathbb{Z}/N\mathbb{Z})$, so it is normal, `CongruenceSubgroup.Gamma_normal`. The edge cases are `CongruenceSubgroup.Gamma_one_top` and `CongruenceSubgroup.Gamma_zero_bot`. The homomorphism $\Gamma_0(N) \to \mathbb{Z}/N\mathbb{Z}$, $g \mapsto d$, is `CongruenceSubgroup.Gamma0Map`.

A congruence subgroup, `CongruenceSubgroup.IsCongruenceSubgroup Γ`, is a subgroup that contains $\Gamma(N)$ for some $N \geq 1$. The three families are congruence subgroups for $N \neq 0$ (`CongruenceSubgroup.Gamma_is_cong_sub`, `CongruenceSubgroup.Gamma1_is_congruence`, `CongruenceSubgroup.Gamma0_is_congruence`), and each congruence subgroup has finite index, `CongruenceSubgroup.IsCongruenceSubgroup.finiteIndex`. Conjugates stay congruence subgroups: `CongruenceSubgroup.conj_cong_is_cong` for conjugation in $\mathrm{SL}_2(\mathbb{Z})$, and `CongruenceSubgroup.exists_Gamma_le_conj` for conjugation by $g \in \mathrm{GL}_2(\mathbb{Q})$, which shows that $g\Gamma(N)g^{-1}$ contains some $\Gamma(M)$. So the conjugate of $\mathrm{SL}_2(\mathbb{Z})$ by an element of $\mathrm{GL}_2(\mathbb{Q})$ is arithmetic, `CongruenceSubgroup.isArithmetic_conj_SL2Z`.

#### Cusps, periods and widths

**Definition.** A point $c \in \mathbb{P}^1(\mathbb{R})$, a term of `OnePoint ℝ`, is a cusp of $\Gamma$, `IsCusp c Γ`, if some parabolic element of $\Gamma$ fixes $c$.

For $\mathrm{SL}_2(\mathbb{Z})$ the cusps are $\mathbb{P}^1(\mathbb{Q})$, by `isCusp_SL2Z_iff`. An arithmetic subgroup has the same cusps, `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`, and the cusps of a subgroup of finite index are those of the larger group, `isCusp_iff_of_relIndex_ne_zero`. The type `CuspOrbits Γ` is the set of orbits of $\Gamma$ on its cusps. For an arithmetic $\Gamma$, `surjective_cosetToCuspOrbit` maps the cosets of $\Gamma \cap \mathrm{SL}_2(\mathbb{Z})$ onto it, so there are only finitely many orbits.

The behaviour at $\infty$ is governed by the translations in $\Gamma$. The strict periods `Subgroup.strictPeriods Γ` are the $h$ with $\begin{pmatrix} 1 & h \\ 0 & 1 \end{pmatrix} \in \Gamma$, and the periods `Subgroup.periods Γ` are the $h$ with $\pm\begin{pmatrix} 1 & h \\ 0 & 1 \end{pmatrix} \in \Gamma$. The strict width `Subgroup.strictWidthInfty Γ` is the least positive strict period, or $0$ if there is none, and `Subgroup.widthInfty Γ` is the same for the periods. If the strict periods are discrete, they are the multiples of the strict width, `Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty`. A group is regular at $\infty$, `Subgroup.IsRegularAtInfty Γ`, if the two groups of periods are equal, for example when $-1 \in \Gamma$ (`Subgroup.isRegularAtInfty_of_neg_one_mem`). Otherwise the index `Subgroup.regularityFactorInfty Γ` is $2$, and `Subgroup.strictWidthInfty_eq_regularityFactorInfty_mul_widthInfty` relates the widths.

| Lean name | Value |
|---|---|
| `Subgroup.widthInfty_SL2Z`, `Subgroup.strictWidthInfty_SL2Z` | $1$ for $\mathrm{SL}_2(\mathbb{Z})$ |
| `CongruenceSubgroup.strictWidthInfty_Gamma0` | $1$ for $\Gamma_0(N)$ |
| `CongruenceSubgroup.strictWidthInfty_Gamma1` | $1$ for $\Gamma_1(N)$ |
| `CongruenceSubgroup.strictWidthInfty_Gamma` | $N$ for $\Gamma(N)$ |

The strict width is the period $h$ of the variable $q = e^{2\pi i z/h}$ in the $q$-expansion of Section 2.

#### Hecke rings

The module `Mathlib.NumberTheory.HeckeRing.Defs` starts the theory of Hecke operators in an abstract form. Let $G$ be a group, $\Delta$ a submonoid and $H_1, H_2$ subgroups. The class `IsHeckeTriple Δ H₁ H₂` asks that $H_1, H_2 \leq \Delta$, that $H_1$ and $H_2$ are commensurable, and that $\Delta$ lies in the commensurator of $H_2$. Then each double coset $H_1 g H_2$ with $g \in \Delta$ is a finite union of left cosets. The type `HeckeCoset Δ H₁ H₂` is the set of these double cosets, with `HeckeCoset.mk`, and `HeckeCosetModule Δ H₁ H₂ Z` is the module of finitely supported $Z$-linear combinations of them. The diagonal case `HeckeRing Δ H Z` is the Hecke ring, and `IsHeckeTriple.of_diagonal` gives its condition. The classical example is $H = \mathrm{SL}_2(\mathbb{Z})$ in $\mathrm{GL}_2(\mathbb{Q})$ with $\Delta$ the integral matrices of positive determinant. The product of double cosets and the action on modular forms are not in this module.

#### Common errors

1. Most modular forms results take a subgroup of `GL (Fin 2) ℝ`, not of `Matrix.SpecialLinearGroup (Fin 2) ℤ`. A congruence subgroup goes there by `Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)`.
2. `CongruenceSubgroup.Gamma 0` is the trivial group, not the whole group, and `CongruenceSubgroup.Gamma0 0` is the group of the matrices with $c = 0$.
3. `Subgroup.strictWidthInfty` and `Subgroup.widthInfty` are different numbers for a group that is not regular at $\infty$: they differ by the factor $2$. The $q$-expansions of Section 2 use the strict periods.

### Exercises

1. (A) Check that $\rho = e^{2\pi i/3}$ is fixed by $ST$, and use `ModularGroup.stabilizer_ρ` to list its stabilizer.
2. (A) Show that $\begin{pmatrix} 1 & 2 \\ 3 & 7 \end{pmatrix}$ lies in $\Gamma_0(3)$ but not in $\Gamma_1(3)$.
3. (B) Compute the index of $\Gamma_0(p)$ in $\mathrm{SL}_2(\mathbb{Z})$ for a prime $p$ from its action on $\mathbb{P}^1(\mathbb{F}_p)$.
4. (B) Show that the cusps $0$ and $\infty$ of $\Gamma_0(p)$ are in different orbits.
5. (C) Use `ModularGroup.exists_smul_mem_fd` and `ModularGroup.cases_of_mem_fd_smul_mem_fd` to show that $S$ and $T$ generate $\mathrm{SL}_2(\mathbb{Z})$.

### Reference

<?reference?>
