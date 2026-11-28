---
title: The class group and the unit theorem
kind: theory
modules:
  - Mathlib.NumberTheory.NumberField.ClassNumber
  - Mathlib.NumberTheory.ClassNumber.Finite
  - Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
  - Mathlib.NumberTheory.NumberField.Units.Basic
  - Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
  - Mathlib.NumberTheory.NumberField.Units.Regulator
  - Mathlib.NumberTheory.NumberField.Cyclotomic.PID
  - Mathlib.NumberTheory.ClassNumber.AdmissibleAbsoluteValue
  - Mathlib.NumberTheory.ClassNumber.AdmissibleAbs
  - Mathlib.NumberTheory.ClassNumber.AdmissibleCardPowDegree
  - Mathlib.NumberTheory.FunctionField
  - Mathlib.NumberTheory.ClassNumber.FunctionField
explains:
  E3: [NumberField.classNumber, NumberField.exists_ideal_in_class_of_norm_le, NumberField.Units.rank, NumberField.Units.exist_unique_eq_mul_prod]
  E2: [NumberField.RingOfIntegers.instFintypeClassGroup, NumberField.classNumber_eq_one_iff, NumberField.classNumber_pos, Rat.classNumber_eq, NumberField.minkowskiNormBound, NumberField.RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt, ClassGroup.fintypeOfAdmissibleOfFinite, IsCyclotomicExtension.Rat.three_pid, IsCyclotomicExtension.Rat.five_pid, IsCyclotomicExtension.Rat.seven_pid, NumberField.InfinitePlace, NumberField.InfinitePlace.IsReal, NumberField.InfinitePlace.IsComplex, NumberField.InfinitePlace.nrRealPlaces, NumberField.InfinitePlace.nrComplexPlaces, NumberField.InfinitePlace.card_add_two_mul_card_eq_rank, NumberField.isUnit_iff_norm, NumberField.Units.torsion, NumberField.Units.mem_torsion, NumberField.Units.torsionOrder, NumberField.Units.torsionOrder_eq_two_of_odd_finrank, NumberField.Units.logEmbedding, NumberField.Units.unitLattice, NumberField.Units.fundSystem, NumberField.Units.finrank_modTorsion]
  E1: auto
families: [NumberField.Units.*, NumberField.InfinitePlace.*]
requires: [V06.C06, V07.C07, V12.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The class group and the unit theorem

### Overview

In $\mathbb{Z}$, every ideal is principal and every unit is $\pm1$. In the ring of integers $\mathcal{O}_K$ of a number field, both facts fail, and two finitely generated abelian groups measure the failure. The class group is the group of the ideals modulo the principal ideals; it is finite, and its order is the class number $h_K$. The unit group $\mathcal{O}_K^\times$ is a finite group of roots of unity times a free abelian group of rank $r_1 + r_2 - 1$, by Dirichlet's unit theorem. This section states both theorems as Mathlib has them, computes $h_K = 2$ for $\mathbb{Q}(\sqrt{-5})$ in full, and connects the unit theorem with Pell's equation of Chapter 4.

The ring $\mathcal{O}_K$ is a Dedekind domain (Section 1): each nonzero ideal is a product of prime ideals in exactly one way. This fact is cited from Mathlib.

### Definitions

**Definition (Class group and class number).** The fractional ideals of $\mathcal{O}_K$ that are invertible form a group under multiplication. The principal fractional ideals $\alpha\mathcal{O}_K$, $\alpha \in K^\times$, form a subgroup. The quotient is the class group $\mathrm{Cl}(K)$, and $h_K = |\mathrm{Cl}(K)|$. Each class contains an integral ideal, and $h_K = 1$ if and only if $\mathcal{O}_K$ is a principal ideal domain.

::: mathlib
`NumberField.classNumber` · `Mathlib.NumberTheory.NumberField.ClassNumber`

`classNumber K = Fintype.card (ClassGroup (𝓞 K))`, with the instance `NumberField.RingOfIntegers.instFintypeClassGroup`. `classNumber_eq_one_iff : classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K)`, `classNumber_pos`, and `Rat.classNumber_eq : classNumber ℚ = 1`. The group `ClassGroup R` of a domain and `ClassGroup.mk0` from nonzero ideals are in `Mathlib.RingTheory.ClassGroup.Basic`.

<?decl NumberField.classNumber?>
:::

**Definition (Infinite places).** An infinite place of $K$ is an absolute value $|\sigma(\cdot)|$ for an embedding $\sigma : K \to \mathbb{C}$. Two embeddings give the same place when they are complex conjugate. A place is real if $\sigma(K) \subseteq \mathbb{R}$ and complex otherwise. With $r_1$ real and $r_2$ complex places, $r_1 + 2r_2 = [K : \mathbb{Q}]$.

::: mathlib
`NumberField.InfinitePlace` · `Mathlib.NumberTheory.NumberField.InfinitePlace.Basic`

`InfinitePlace K`, with the predicates `IsReal` and `IsComplex`, the counts `nrRealPlaces K` and `nrComplexPlaces K`, and `card_add_two_mul_card_eq_rank : nrRealPlaces K + 2 * nrComplexPlaces K = finrank ℚ K`.

<?decl NumberField.InfinitePlace?>
:::

**Definition (Torsion and unit rank).** The torsion subgroup $\mu_K$ of $\mathcal{O}_K^\times$ is the set of roots of unity in $K$. The unit rank is $r = r_1 + r_2 - 1$, the number of infinite places minus one.

::: mathlib
`NumberField.Units.rank` · `Mathlib.NumberTheory.NumberField.Units.DirichletTheorem`

`Units.rank K = Fintype.card (InfinitePlace K) - 1`. The torsion is `Units.torsion K`, a finite cyclic subgroup, with `mem_torsion : x ∈ torsion K ↔ ∀ w, w x = 1` and order `torsionOrder K`. For $K$ of odd degree, `torsionOrder_eq_two_of_odd_finrank`.

<?decl NumberField.Units.rank?>
:::

### Theorems and proofs

**Theorem (Minkowski bound, cited).** Let $K$ have degree $n$ and $r_2$ complex places. Every class of $\mathrm{Cl}(K)$ contains an integral ideal $I$ with
$$N(I) \le M_K = \left(\frac4\pi\right)^{r_2}\frac{n!}{n^n}\sqrt{|d_K|}.$$
Since there are only finitely many integral ideals of a given norm, $\mathrm{Cl}(K)$ is finite.

The proof applies Minkowski's theorem on convex bodies to the lattice of an ideal in $\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$. It is not given here.

::: mathlib
`NumberField.exists_ideal_in_class_of_norm_le` · `Mathlib.NumberTheory.NumberField.ClassNumber`

`∀ C : ClassGroup (𝓞 K), ∃ I, ClassGroup.mk0 I = C ∧ absNorm I ≤ minkowskiNormBound K`. A corollary is `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt`, which gives $h_K = 1$ when $M_K < 2$. The finiteness of the class group in the general setting of a finite extension of the fraction field of a Euclidean domain is `ClassGroup.fintypeOfAdmissibleOfFinite` in `Mathlib.NumberTheory.ClassNumber.Finite`; this covers function fields as well.

<?decl NumberField.exists_ideal_in_class_of_norm_le?>
:::

**Theorem.** The class number of $K = \mathbb{Q}(\sqrt{-5})$ is $2$.

*Proof.* By Section 1, $\mathcal{O}_K = \mathbb{Z}[\sqrt{-5}]$ and $d_K = -20$. Here $n = 2$ and $r_2 = 1$, so $M_K = \frac4\pi\cdot\frac24\cdot\sqrt{20} = \frac{4\sqrt5}{\pi} \approx 2.85$. Every class contains an integral ideal of norm $1$ or $2$.

The ideal of norm $1$ is $\mathcal{O}_K$, the trivial class. Let $I$ have norm $2$, so $\mathcal{O}_K/I$ has order $2$. Then $I$ is maximal and contains $2$. Let $P = (2, 1 + \sqrt{-5})$. The quotient $\mathcal{O}_K/P$ is $\mathbb{Z}/2$: modulo $P$, $\sqrt{-5} \equiv -1 \equiv 1$, and $P \ne \mathcal{O}_K$ since every element $2(a + b\sqrt{-5}) + (1 + \sqrt{-5})(c + e\sqrt{-5})$ of $P$ has the form $x + y\sqrt{-5}$ with $x \equiv y \pmod 2$. So $P$ has norm $2$. Next,
$$P^2 = (4,\ 2 + 2\sqrt{-5},\ (1 + \sqrt{-5})^2) = (4,\ 2 + 2\sqrt{-5},\ -4 + 2\sqrt{-5}).$$
Each generator is divisible by $2$, and $P^2$ contains $(2 + 2\sqrt{-5}) - (-4 + 2\sqrt{-5}) - 4 = 2$. So $P^2 = (2)$. The maximal ideal $I$ contains $P^2$, so it contains $P$, and $I = P$ since both have index $2$.

The ideal $P$ is not principal. If $P = (\alpha)$, then $|N(\alpha)| = N(P) = 2$, and $\alpha = a + b\sqrt{-5}$ gives $a^2 + 5b^2 = 2$, which has no integer solution. So $\mathrm{Cl}(K) = \{[\mathcal{O}_K], [P]\}$ with $[P] \ne 1$ and $[P]^2 = [(2)] = 1$, and $h_K = 2$. $\square$

**Proposition (The kernel of the logarithm).** Let $L : \mathcal{O}_K^\times \to \mathbb{R}^{r_1 + r_2}$, $L(u) = (m_w\log w(u))_w$ with $m_w = 1$ for real and $m_w = 2$ for complex places. Then $\ker L = \mu_K$, and $\mu_K$ is finite.

*Proof.* A root of unity $\zeta$ has $w(\zeta) = 1$ for each $w$, so $\mu_K \subseteq \ker L$. Conversely, let $S$ be the set of $\alpha \in \mathcal{O}_K$ with $|\sigma(\alpha)| \le 1$ for all embeddings $\sigma$. For $\alpha \in S$, the characteristic polynomial $\prod_\sigma(X - \sigma(\alpha))$ has integer coefficients, and the coefficient of $X^{n-k}$ has absolute value at most $\binom nk$. There are finitely many such polynomials, each with at most $n$ roots, so $S$ is finite. The kernel of $L$ is a subgroup contained in $S$, so it is a finite group, and each of its elements has finite order, so it is a root of unity. $\square$

**Theorem (Dirichlet's unit theorem, cited in part).** $\mathcal{O}_K^\times \cong \mu_K \times \mathbb{Z}^r$ with $r = r_1 + r_2 - 1$. There are fundamental units $\varepsilon_1, \dots, \varepsilon_r$ such that every unit is uniquely $\zeta\varepsilon_1^{e_1}\cdots\varepsilon_r^{e_r}$ with $\zeta \in \mu_K$ and $e_i \in \mathbb{Z}$.

*About the proof.* By the norm (Section 1), $\prod_w w(u)^{m_w} = |N(u)| = 1$, so the image of $L$ lies in the hyperplane $H = \{\sum_w x_w = 0\}$ of dimension $r$. The argument of the proposition, with the bound $e^R$ instead of $1$, shows that $L(\mathcal{O}_K^\times)$ meets each ball in a finite set, so it is a lattice of rank at most $r$ in $H$. By the proposition, $\mathcal{O}_K^\times/\mu_K \cong L(\mathcal{O}_K^\times)$ is free (Volume 7, Chapter 7). That the rank is exactly $r$ needs units with prescribed sizes at the places, and these come from Minkowski's theorem; this step is cited.

::: mathlib
`NumberField.Units.exist_unique_eq_mul_prod` · `Mathlib.NumberTheory.NumberField.Units.DirichletTheorem`

`∀ x : (𝓞 K)ˣ, ∃! ζe : torsion K × (Fin (rank K) → ℤ), x = ζe.1 * ∏ i, fundSystem K i ^ ζe.2 i`. The units `fundSystem K` are a chosen system of fundamental units. The rank statement is `finrank_modTorsion : finrank ℤ (Additive ((𝓞 K)ˣ ⧸ torsion K)) = rank K`. The proof in Mathlib uses `logEmbedding K` and the lattice `unitLattice K`. A unit test over `ℚ` is `NumberField.isUnit_iff_norm : IsUnit x ↔ |N x| = 1`.

<?decl NumberField.Units.exist_unique_eq_mul_prod?>
:::

### Examples

**Example (Imaginary quadratic fields).** For $K = \mathbb{Q}(\sqrt d)$ with $d < 0$, $r_1 = 0$ and $r_2 = 1$, so $r = 0$ and $\mathcal{O}_K^\times = \mu_K$ is finite: of order $4$ for $d = -1$, $6$ for $d = -3$, and $2$ otherwise (Section 1, Exercise 4).

**Example (Real quadratic fields and Pell).** For $d > 1$ squarefree, $r_1 = 2$ and $r_2 = 0$, so $r = 1$ and $\mathcal{O}_K^\times = \{\pm\varepsilon^n\}$. For $d \equiv 2, 3 \pmod 4$, the units of norm $1$ are the solutions of $x^2 - dy^2 = 1$, and Section 4.3 proved directly that they are $\pm\varepsilon_0^n$ with $\varepsilon_0$ the fundamental solution. For $d = 2$, $\varepsilon = 1 + \sqrt2$ has norm $-1$ and $\varepsilon^2 = 3 + 2\sqrt2$ is the fundamental solution of $x^2 - 2y^2 = 1$.

**Example (Class number one by the bound).** For $K = \mathbb{Q}(i)$, $M_K = \frac4\pi\cdot\frac12\cdot\sqrt4 = \frac4\pi < 2$, so $h_K = 1$ and $\mathbb{Z}[i]$ is a PID, in accordance with Volume 6, Chapter 6. For $\mathbb{Q}(\sqrt{-3})$, $M_K = \frac{2\sqrt3}{\pi} \approx 1.10$, so $h_K = 1$ too.

**Counterexample (Unique factorization fails).** In $\mathbb{Z}[\sqrt{-5}]$, $6 = 2\cdot3 = (1 + \sqrt{-5})(1 - \sqrt{-5})$ with four irreducible factors that are not associate (Volume 6, Chapter 6). As ideals, $(2) = P^2$, $(3) = QQ'$ and $(1 \pm \sqrt{-5}) = PQ$, $PQ'$, with $Q = (3, 1 + \sqrt{-5})$ and $Q' = (3, 1 - \sqrt{-5})$; both factorizations of $6$ are the same product $P^2QQ'$ of prime ideals.

### The library around it

`Mathlib.NumberTheory.NumberField.Cyclotomic.PID` proves that the rings of integers of $\mathbb{Q}(\zeta_3)$, $\mathbb{Q}(\zeta_5)$ and $\mathbb{Q}(\zeta_7)$ are PIDs (`IsCyclotomicExtension.Rat.three_pid`, `five_pid`, `seven_pid`) with the Minkowski bound. The index of this edition has no declaration for the class number formula of Dirichlet or for the class numbers of quadratic fields beyond these cases.

`Mathlib.NumberTheory.NumberField.Units.Regulator` defines the regulator. For a family $u_1, \dots, u_r$ of units, with $r$ the unit rank, `NumberField.Units.regOfFamily u` is the absolute value of the determinant of the matrix $(m_w \log w(u_i))$, with $i \le r$ and $w$ over the places other than one fixed place $w'$ (`NumberField.Units.regOfFamily_eq_det`). The value does not depend on the choice of $w'$, because the sum of the columns over all places is zero. The family has maximal rank (`NumberField.Units.IsMaxRank u`) when the subgroup it generates has finite index (`NumberField.Units.isMaxRank_iff_closure_finiteIndex`). The regulator `NumberField.Units.regulator K` is the value at a fundamental system (`NumberField.Units.regulator_eq_regOfFamily_fundSystem`, `NumberField.Units.regulator_eq_det`), and it is positive (`NumberField.Units.regulator_pos`). For any family, `NumberField.Units.regOfFamily_div_regulator` gives $\mathrm{Reg}(u)/R_K = [\mathcal{O}_K^\times : \langle u \rangle \mu_K]$. Here the index is $0$ when it is infinite, and then $\mathrm{Reg}(u) = 0$. Section 3 uses the regulator for the volume of a fundamental domain of the units, and Section 4 compares the regulators of a CM field and its maximal real subfield.

The proof of `ClassGroup.fintypeOfAdmissibleOfFinite` needs an admissible absolute value on the base ring, the structure `AbsoluteValue.IsAdmissible abv` of `Mathlib.NumberTheory.ClassNumber.AdmissibleAbsoluteValue`. An absolute value $\lvert\cdot\rvert : R \to \mathbb{Z}$ on a Euclidean domain is admissible when, for each $\varepsilon > 0$ and $b \neq 0$, any family of elements of $R$ splits into at most `AbsoluteValue.IsAdmissible.card` classes such that two members $a_0, a_1$ of the same class have $\lvert (a_1 \bmod b) - (a_0 \bmod b) \rvert < \varepsilon\lvert b \rvert$. This pigeonhole property is `AbsoluteValue.IsAdmissible.exists_partition`, and `AbsoluteValue.IsAdmissible.exists_approx` is the form for tuples that the proof uses. It replaces the volume argument of Minkowski, so it works for function fields too. The two instances are `AbsoluteValue.absIsAdmissible` for the usual absolute value on `ℤ`, from `AbsoluteValue.exists_partition_int` in `Mathlib.NumberTheory.ClassNumber.AdmissibleAbs`, and `Polynomial.cardPowDegreeIsAdmissible` for $\lvert f \rvert = q^{\deg f}$ on $\mathbb{F}_q[X]$, from `Polynomial.exists_approx_polynomial` and the ultrametric inequality `Polynomial.cardPowDegree_anti_archimedean` in `Mathlib.NumberTheory.ClassNumber.AdmissibleCardPowDegree`. The module `Mathlib.NumberTheory.FunctionField` defines the function fields: `FunctionField Fq F` says that $F$ is a finite extension of the field of rational functions `RatFunc Fq`, with `functionField_iff` for any other model of that field, and `FunctionField.ringOfIntegers Fq F` is the integral closure of $\mathbb{F}_q[X]$ in $F$. This ring is a Dedekind domain when $F$ is separable over `RatFunc Fq`, and it is not a field by `FunctionField.ringOfIntegers.not_isField`. For a finite field $\mathbb{F}_q$, the module `Mathlib.NumberTheory.ClassNumber.FunctionField` applies the general theorem with `Polynomial.cardPowDegreeIsAdmissible`: the class group of `FunctionField.ringOfIntegers Fq F` is finite, `FunctionField.classNumber Fq F` is its order, and `FunctionField.classNumber_eq_one_iff` says that it is $1$ if and only if the ring is a PID.

Common errors of a learner:

- `ClassGroup (𝓞 K)` uses the invertible fractional ideals, and `ClassGroup.mk0` takes a nonzero integral ideal as an element of `nonZeroDivisors (Ideal (𝓞 K))`.
- `Units.rank K` is a natural number defined with a subtraction; for $K = \mathbb{Q}$ it is $1 - 1 = 0$.

### Exercises

1. (A) Compute the Minkowski bound of $\mathbb{Q}(\sqrt{-2})$, $\mathbb{Q}(\sqrt{-7})$ and $\mathbb{Q}(\sqrt2)$, and deduce that their class numbers are $1$.
2. (A) Find $r_1$, $r_2$ and the unit rank of $\mathbb{Q}(\sqrt[3]2)$ and of $\mathbb{Q}(\zeta_5)$.
3. (A) Check the ideal equations $(3) = QQ'$ and $(1 + \sqrt{-5}) = PQ$ of the counterexample.
4. (B) Show that $\mathbb{Q}(\sqrt{-6})$ has class number $2$, by the method used for $\mathbb{Q}(\sqrt{-5})$.
5. (B) Show that the fundamental unit of $\mathbb{Q}(\sqrt5)$ is $\varphi = \frac{1 + \sqrt5}{2}$, and find the fundamental solution of $x^2 - 5y^2 = 1$ from it.
6. (B) Show that if $h_K$ is odd and $I^2$ is principal, then $I$ is principal.
7. (C) Let $p \equiv 1 \pmod 4$ be prime. Use $h_{\mathbb{Q}(i)} = 1$ to show again that $p$ is a sum of two squares, through the factorization of the ideal $(p)$ in $\mathbb{Z}[i]$.

### Notes and history

Gauss computed class numbers in the language of binary quadratic forms in the *Disquisitiones Arithmeticae* of 1801. Kummer showed that his ideal numbers restore unique factorization in cyclotomic rings and proved Fermat's last theorem for the regular primes, those that do not divide the class number of $\mathbb{Q}(\zeta_p)$. Dirichlet proved the unit theorem in 1846. Minkowski's geometry of numbers from the 1890s gave the bound used here. A reference is Marcus, *Number Fields*, Chapter 5, and Neukirch, *Algebraic Number Theory*, Chapter I, Sections 6 and 7.

### Reference

<?reference?>
