---
title: The spectrum and the quasispectrum of an element
kind: api
modules:
  - Mathlib.Algebra.Algebra.Spectrum.Basic
  - Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
  - Mathlib.Algebra.Algebra.Spectrum.Pi
explains:
  E2: [spectrum.mem_iff, spectrum.zero_mem_iff, spectrum.nonzero_mul_comm, spectrum.add_singleton_eq, spectrum.resolvent_sub_resolvent, AlgHom.spectrum_apply_subset, AlgHom.apply_mem_spectrum, isQuasiregular_iff_isUnit, Unitization.quasispectrum_eq_spectrum_inr, Pi.spectrum_eq]
  E1: auto
families: []
requires: [V06.C01, V06.C03, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The spectrum and the quasispectrum of an element

### Overview

The spectrum of a square matrix is its set of eigenvalues. For an element $a$ of an $R$-algebra $A$ the same idea gives the spectrum $\sigma(a)$: the set of scalars $r$ such that $r - a$ is not invertible in $A$. For a matrix over a field this is the set of eigenvalues, because a square matrix is invertible exactly when it has no kernel. In infinite dimensions the spectrum can contain points that are not eigenvalues, and spectral theory in Volume 16 studies it with analysis.

This section gives the algebraic part of the theory, which needs no topology. It proves the rules for the spectrum of $a + r$, $ra$, $a^{-1}$, $ab$ and $f(a)$ under an algebra map, and the resolvent identity. Then it defines the quasispectrum, the form of the spectrum for a non-unital algebra, through quasiregular elements. The section needs the algebras of Section 1, the units of Chapter 3 and the unitization of Section 11.

### The library around it

#### The definitions

Let $R$ be a commutative ring and $A$ an $R$-algebra. Write $\uparrow r$ for `algebraMap R A r`. The resolvent set `resolventSet R a` is the set of $r \in R$ such that $\uparrow r - a$ is a unit, and the spectrum `spectrum R a` is its complement. The theorem `spectrum.mem_iff` states $r \in \sigma(a) \iff \neg \operatorname{IsUnit}(\uparrow r - a)$, and `spectrum.notMem_iff` and `spectrum.mem_resolventSet_iff` are the other forms. The resolvent `resolvent a r` is the inverse $(\uparrow r - a)^{-1}$, with the junk value of `Ring.inverse` outside the resolvent set. The lemma `spectrum.isUnit_resolvent` says that $r$ is in the resolvent set exactly when the resolvent is a unit.

The scalar ring is explicit: the spectrum of $a$ over $\mathbb{R}$ and over $\mathbb{C}$ are different sets. For a tower $R \to S \to A$, `spectrum.preimage_algebraMap` says that $\sigma_R(a)$ is the preimage of $\sigma_S(a)$, and `spectrum.algebraMap_mem_iff` is the pointwise form. For example the rotation matrix $\begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$ has the spectrum $\{i, -i\}$ over $\mathbb{C}$ and the empty spectrum over $\mathbb{R}$.

#### Zero and the units

The theorem `spectrum.zero_mem_iff` says $0 \in \sigma(a)$ exactly when $a$ is not a unit. Proof: $\uparrow 0 - a = -a$, and $-a$ is a unit exactly when $a$ is. So `Units.zero_notMem_spectrum` says that the spectrum of a unit misses $0$, and `spectrum.zero_notMem_iff` is the converse form. In a nonzero algebra, `spectrum.zero_eq`, `spectrum.one_eq` and `spectrum.scalar_eq` give $\sigma(0) = \{0\}$, $\sigma(1) = \{1\}$ and $\sigma(\uparrow k) = \{k\}$ over a field. In the zero algebra each element is a unit, so `spectrum.of_subsingleton` says that the spectrum is empty.

The spectrum of the inverse is the set of inverses. Over a field, `spectrum.map_inv` says $\sigma(a^{-1}) = \sigma(a)^{-1}$ for a unit $a$, and `spectrum.inv₀_mem_iff` is the pointwise form. Proof: for $r \neq 0$, $\uparrow r - a^{-1} = -\uparrow r \, a^{-1} (\uparrow r^{-1} - a)$, and the first two factors are units. So $\uparrow r - a^{-1}$ is a unit exactly when $\uparrow r^{-1} - a$ is.

#### Translation, scaling and products

The spectrum moves with the element.

| Lean name | Statement |
| --- | --- |
| `spectrum.add_singleton_eq` | $\sigma(a) + \{r\} = \sigma(a + \uparrow r)$ |
| `spectrum.singleton_add_eq` | $\{r\} + \sigma(a) = \sigma(\uparrow r + a)$ |
| `spectrum.neg_eq` | $-\sigma(a) = \sigma(-a)$ |
| `spectrum.unit_smul_eq_smul` | $\sigma(u a) = u \, \sigma(a)$ for a unit $u$ of $R$ |
| `spectrum.smul_eq_smul` | $\sigma(k a) = k \, \sigma(a)$ over a field, when $\sigma(a) \neq \emptyset$ |
| `spectrum.units_conjugate` | $\sigma(u a u^{-1}) = \sigma(a)$ for a unit $u$ of $A$ |

The proof of `spectrum.add_singleton_eq` is one line: $\uparrow(s + r) - (a + \uparrow r) = \uparrow s - a$, so $s \in \sigma(a)$ exactly when $s + r \in \sigma(a + \uparrow r)$. The hypothesis of `spectrum.smul_eq_smul` covers $k = 0$: then $\sigma(0 \cdot a) = \{0\}$, and $0 \cdot \sigma(a)$ is $\{0\}$ only when $\sigma(a)$ is not empty.

The spectra of $ab$ and $ba$ agree away from $0$. The theorem `spectrum.nonzero_mul_comm` says $\sigma(ab) \setminus \{0\} = \sigma(ba) \setminus \{0\}$ over a field, and `spectrum.unit_mem_mul_comm` says the same for units of a ring. The proof uses Jacobson's lemma: $1 - ab$ is a unit exactly when $1 - ba$ is. If $c$ is the inverse of $1 - ab$, then $1 + bca$ is the inverse of $1 - ba$, because
$$(1 - ba)(1 + bca) = 1 - ba + b(1 - ab)ca = 1 - ba + ba = 1,$$
and in the same way on the other side. For $r \neq 0$ apply this to $r^{-1} a$ and $b$. The value $0$ can differ: the shift operators $S, T$ on sequences with $TS = 1$ and $ST \neq 1$ give $0 \notin \sigma(TS)$ and $0 \in \sigma(ST)$.

#### The resolvent identity

The theorem `spectrum.resolvent_sub_resolvent` is the first resolvent identity in a form for two elements:
$$R_a(r) - R_b(r) = R_a(r) (a - b) R_b(r),$$
where $R_a(r) = (r - a)^{-1}$. Proof: multiply $(r - b) - (r - a) = a - b$ by $R_a(r)$ on the left and by $R_b(r)$ on the right. The lemma `spectrum.units_smul_resolvent` relates the resolvent of $a$ at $r s$ to the resolvent of $s^{-1} a$. Analysis uses these identities to prove that the resolvent is analytic and that the spectrum is closed.

#### Algebra maps

An algebra map can only shrink the spectrum. The theorem `AlgHom.spectrum_apply_subset` says $\sigma(\phi(a)) \subseteq \sigma(a)$. Proof: if $\uparrow r - a$ is a unit, then its image $\uparrow r - \phi(a)$ is a unit. An isomorphism keeps the spectrum, by `AlgEquiv.spectrum_eq`. The same argument gives `spectrum.subset_subalgebra`: the spectrum of $a$ in $A$ is contained in the spectrum of $a$ in a subalgebra, since an inverse in the subalgebra is an inverse in $A$. The inclusion can be strict.

A character is an algebra map $\phi : A \to R$. The theorem `AlgHom.apply_mem_spectrum` says that $\phi(a) \in \sigma(a)$ for each character. Proof: $\phi(\uparrow \phi(a) - a) = \phi(a) - \phi(a) = 0$, and $0$ is not a unit in the nonzero ring $R$. So $\uparrow \phi(a) - a$ is not a unit. In a commutative Banach algebra the characters give the whole spectrum, which is the start of Gelfand theory.

The module `Mathlib.Algebra.Algebra.Spectrum.Pi` computes spectra in products. `Pi.spectrum_eq` says $\sigma((a_i)_i) = \bigcup_i \sigma(a_i)$, and `Prod.spectrum_eq` says $\sigma((a, b)) = \sigma(a) \cup \sigma(b)$. Proof: a family is a unit exactly when each coordinate is a unit, so $\uparrow r - (a_i)$ fails to be a unit exactly when some $\uparrow r - a_i$ fails. The module also gives `Pi.quasispectrum_eq` and `Prod.quasispectrum_eq`, and `isQuasiregular_pi_iff` and `isQuasiregular_prod_iff`.

#### Quasiregular elements

A non-unital algebra has no units, so the definition of the spectrum must change. The circle product $x \circ y = x + y + xy$ is associative with neutral element $0$. In a unital ring $1 + (x \circ y) = (1 + x)(1 + y)$, so the circle product is the product of $1 + x$ and $1 + y$ shifted by $1$. The type `PreQuasiregular R` is a copy of $R$ with the circle product as its multiplication, and `IsQuasiregular x` says that $x$ is a unit for it. The theorem `isQuasiregular_iff` says this: there is $y$ with $y + x + xy = 0$ and $x + y + yx = 0$. In a unital ring, `isQuasiregular_iff_isUnit` says that $x$ is quasiregular exactly when $1 + x$ is a unit. Proof: by the identity $1 + (x \circ y) = (1 + x)(1 + y)$, an inverse $y$ of $x$ for $\circ$ gives the inverse $1 + y$ of $1 + x$, and conversely.

The quasispectrum `quasispectrum R a` is the set of $r$ such that $r$ is not a unit of $R$, or $r$ is a unit and $-r^{-1} a$ is not quasiregular. In a unital algebra, for a unit $r$, $1 - r^{-1} a$ is a unit exactly when $r - a$ is, so the quasispectrum is the spectrum with the nonunits of $R$ added: `quasispectrum_eq_spectrum_union` says this. Over a field this is $\sigma(a) \cup \{0\}$, by `quasispectrum_eq_spectrum_union_zero`, and `mem_quasispectrum_iff` is the pointwise form. So `quasispectrum.zero_mem` says $0$ is always in the quasispectrum, and `spectrum_subset_quasispectrum` says that the spectrum is a subset.

The unitization connects the two notions. The theorem `Unitization.quasispectrum_eq_spectrum_inr` says that the quasispectrum of $a \in A$ equals the spectrum of $(0, a)$ in `Unitization R A`, over a field. Proof sketch: for $r \neq 0$, the element $(r, -a) = r(1, -r^{-1}a)$ is a unit exactly when $-r^{-1}a$ is quasiregular in $A$, by the identity for the circle product; and $0$ is in both sets because $(0, -a)$ is never a unit, its first coordinate being $0$. The more general `Unitization.spectrum_eq_vadd_quasispectrum` says $\sigma((r, a)) = r + \sigma'(a)$. The multiplicative equivalence `Unitization.unitsFstOne_mulEquiv_quasiregular` identifies the units of the unitization with first coordinate $1$ and the quasiregular elements of $A$.

The rest of the quasispectrum API repeats the spectrum API. `quasispectrum.mul_comm` says $\sigma'(ab) = \sigma'(ba)$, with no exception at $0$ since $0$ lies in both. `NonUnitalAlgHom.quasispectrum_apply_subset` says that a non-unital map shrinks the quasispectrum.

#### Restriction of the scalars

Spectral theory often needs the spectrum over a smaller field. If $a$ is self-adjoint in a C*-algebra, then its complex spectrum is real, and the continuous functional calculus wants it as a subset of $\mathbb{R}$. The predicate `SpectrumRestricts a f` says that $f : S \to R$ is a left inverse of `algebraMap R S` and a right inverse of it on $\sigma_S(a)$. The theorem `spectrumRestricts_iff` states this, and `SpectrumRestricts.of_subset_range_algebraMap` gives it when the spectrum lies in the image of $R$. `QuasispectrumRestricts` is the version for the quasispectrum. The class `NonnegSpectrumClass 𝕜 A` says that the quasispectrum of each nonnegative element is nonnegative, for an ordered algebra $A$.

#### Common errors

1. `spectrum R a` depends on $R$. The spectrum over `ℝ` of an element of a complex algebra is computed through `algebraMap ℝ ℂ`, and `spectrum.preimage_algebraMap` gives the relation. A lemma about `spectrum ℂ a` does not apply to `spectrum ℝ a`.
2. `spectrum.smul_eq_smul` has the hypothesis that $\sigma(a)$ is nonempty, because the statement includes $k = 0$. Over a field that is not algebraically closed the spectrum can be empty, so this hypothesis is not automatic. For a unit scalar, use `spectrum.unit_smul_eq_smul`, which has no such hypothesis.
3. The quasispectrum always contains $0$ over a field, also for a unit $a$. Use the spectrum when the question is whether $0$ is a spectral value.

### Exercises

1. (A) Compute the spectrum of the diagonal matrix with entries $1, 2, 2$ over $\mathbb{Q}$ with `Pi.spectrum_eq`, by seeing the diagonal matrices as a product.
2. (A) Prove `spectrum.neg_eq` from `spectrum.mem_iff`.
3. (B) Show that a nilpotent element $a$ of a nonzero algebra over a field has $\sigma(a) = \{0\}$.
4. (B) Prove Jacobson's lemma: if $1 - ab$ has the inverse $c$, then $1 + bca$ is the inverse of $1 - ba$, on both sides.
5. (B) Prove that the circle product $x \circ y = x + y + xy$ is associative in any non-unital ring.
6. (C) Let $\phi : A \to B$ be an injective algebra map. Give an example with $\sigma(\phi(a)) \neq \sigma(a)$.

### Reference

<?reference?>
