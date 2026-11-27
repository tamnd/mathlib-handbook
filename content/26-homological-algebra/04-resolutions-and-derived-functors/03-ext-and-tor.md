---
title: Ext and Tor
kind: theory
modules:
  - Mathlib.CategoryTheory.Abelian.Ext
  - Mathlib.CategoryTheory.Monoidal.Tor
  - Mathlib.CategoryTheory.Abelian.Projective.Dimension
  - Mathlib.CategoryTheory.Abelian.Injective.Dimension
  - Mathlib.CategoryTheory.Abelian.Projective.Ext
  - Mathlib.CategoryTheory.Abelian.Injective.Ext
explains:
  E3: [CategoryTheory.Tor, CategoryTheory.ProjectiveResolution.extEquivCohomologyClass, CategoryTheory.ProjectiveResolution.extMk, CategoryTheory.ProjectiveResolution.extMk_surjective, CategoryTheory.ProjectiveResolution.extMk_eq_zero_iff, CategoryTheory.InjectiveResolution.extMk, CategoryTheory.HasProjectiveDimensionLT, CategoryTheory.projectiveDimension, CategoryTheory.projective_iff_subsingleton_ext_one, CategoryTheory.HasInjectiveDimensionLT, CategoryTheory.injectiveDimension]
  E2: [CategoryTheory.Tor', CategoryTheory.isZero_Tor_succ_of_projective, CategoryTheory.isZero_Tor'_succ_of_projective, CategoryTheory.ProjectiveResolution.extAddEquivCohomologyClass, CategoryTheory.ProjectiveResolution.extLinearEquivCohomologyClass, CategoryTheory.ProjectiveResolution.add_extMk, CategoryTheory.ProjectiveResolution.extMk_comp_mk₀, CategoryTheory.InjectiveResolution.extEquivCohomologyClass, CategoryTheory.InjectiveResolution.extMk_surjective, CategoryTheory.InjectiveResolution.extMk_eq_zero_iff, CategoryTheory.InjectiveResolution.extLinearEquivCohomologyClass, CategoryTheory.HasProjectiveDimensionLE, CategoryTheory.hasProjectiveDimensionLT_iff, CategoryTheory.projective_iff_hasProjectiveDimensionLT_one, CategoryTheory.projectiveDimension_le_iff, CategoryTheory.projectiveDimension_eq_zero_iff, CategoryTheory.projectiveDimension_ne_top_iff, CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff, CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₂, CategoryTheory.HasInjectiveDimensionLE, CategoryTheory.injective_iff_subsingleton_ext_one, CategoryTheory.injectiveDimension_le_iff, CategoryTheory.ShortComplex.ShortExact.hasInjectiveDimensionLT_X₁]
  E1: auto
families: []
requires: [V24.C07, V24.C08, V25.C02, V26.C01, V26.C02, V26.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Ext and Tor

### Overview

The two derived functors that occur most often are those of $\operatorname{Hom}$ and of the tensor product. $\operatorname{Ext}^n(X, Y)$ is the $n$-th cohomology of $\operatorname{Hom}(P, Y)$ for a projective resolution $P$ of $X$, and $\operatorname{Tor}_n(X, Y)$ is the $n$-th homology of $X \otimes P$ for a projective resolution $P$ of $Y$. Ext classifies extensions and measures the failure of $\operatorname{Hom}(X, -)$ to be right exact. Tor measures the failure of $X \otimes -$ to be left exact, and over $\mathbb{Z}$ it detects torsion, which gives the name.

This section defines both, proves that $\operatorname{Ext}^0 = \operatorname{Hom}$, the long exact sequence of Ext in the second variable, and that an object is projective if and only if $\operatorname{Ext}^1(X, -) = 0$. It defines the projective and injective dimension and proves that the projective dimension is the minimal length of a projective resolution. It computes $\operatorname{Ext}^1(\mathbb{Z}/n, \mathbb{Z}) = \mathbb{Z}/n$ and $\operatorname{Tor}_1(\mathbb{Z}/m, \mathbb{Z}/n) = \mathbb{Z}/\gcd(m, n)$.

Mathlib now defines Ext by morphisms in the derived category. That definition is the subject of Chapter 5. The files of this section connect it to resolutions: they prove that the derived category Ext is the cohomology of $\operatorname{Hom}(P, Y)$, or of $\operatorname{Hom}(X, I)$ for an injective resolution $I$ of $Y$. This section works with that description and refers to Chapter 5 for the rest. Monoidal categories are from Volume 24, Chapter 7.

### Definitions

The category $C$ is abelian with enough projectives, and $X, Y$ are objects of $C$.

**Definition (Ext by a projective resolution).** Let $P \to X$ be a projective resolution. The groups $\operatorname{Hom}(P_k, Y)$ with the maps $d_{k+1}^\ast : \operatorname{Hom}(P_k, Y) \to \operatorname{Hom}(P_{k+1}, Y)$, $f \mapsto f d_{k+1}$, form a cochain complex $\operatorname{Hom}(P, Y)$ of abelian groups. Set
$$\operatorname{Ext}^n(X, Y) = H^n(\operatorname{Hom}(P, Y)).$$
A class in degree $n$ is represented by a *cocycle* $f : P_n \to Y$ with $f d_{n+1} = 0$, and $f$ represents zero if and only if $f = g d_n$ for some $g : P_{n-1} \to Y$. In degree $0$ every $f$ with $f d_1 = 0$ is a cocycle and only $0$ is a coboundary.

By the independence theorem of Section 2, applied to the contravariant additive functor $\operatorname{Hom}(-, Y)$, this group does not depend on $P$. It is a right derived functor of $\operatorname{Hom}(-, Y)$, computed in $C^{\mathrm{op}}$, where $P$ becomes an injective resolution. If $C$ is $R$-linear, the groups are $R$-modules.

**Definition (Tor).** Let $C$ be a monoidal abelian category in which $\otimes$ is additive in each variable, with enough projectives. For $X$ in $C$, the functor $X \otimes -$ is additive, and
$$\operatorname{Tor}_n(X, Y) = L_n(X \otimes -)(Y).$$
The left derived functors in the first variable define $\operatorname{Tor}'_n(X, Y) = L_n(- \otimes Y)(X)$.

**Definition (Projective and injective dimension).** The object $X$ has *projective dimension $< n$* if $\operatorname{Ext}^i(X, Y) = 0$ for all $Y$ and all $i \geq n$. The *projective dimension* $\operatorname{pd} X$ is the infimum of the $n$ with $\operatorname{pd} X < n + 1$, in $\{-\infty\} \cup \mathbb{N} \cup \{\infty\}$. Dually, $Y$ has *injective dimension $< n$* if $\operatorname{Ext}^i(X, Y) = 0$ for all $X$ and all $i \geq n$.

The value $-\infty$ belongs to the zero object only: $\operatorname{pd} X < 0$ means $\operatorname{Ext}^0(X, X) = \operatorname{Hom}(X, X) = 0$.

::: mathlib
`CategoryTheory.ProjectiveResolution.extMk` · `Mathlib.CategoryTheory.Abelian.Projective.Ext`

For `R : ProjectiveResolution X`, a map `f : R.complex.X n ⟶ Y` with `R.complex.d m n ≫ f = 0` and `n + 1 = m` gives `R.extMk f m hm hf : Ext X Y n`. Here `Ext` is `CategoryTheory.Abelian.Ext`, the derived category Ext of Chapter 5. `extMk_surjective` says that each class has this form, and `extMk_eq_zero_iff` says that the class is zero exactly when `f = R.complex.d n p ≫ g` with `p + 1 = n`. Together they are the description of Ext by cocycles and coboundaries. The bundled form is `R.extEquivCohomologyClass`, with additive and linear versions.

<?decl CategoryTheory.ProjectiveResolution.extMk?>
:::

### Theorems and proofs

**Proposition ($\operatorname{Ext}^0$ is $\operatorname{Hom}$).** There is a natural isomorphism $\operatorname{Ext}^0(X, Y) \cong \operatorname{Hom}(X, Y)$.

*Proof.* By definition $\operatorname{Ext}^0(X, Y) = \{f : P_0 \to Y : f d_1 = 0\}$. The sequence $P_1 \to P_0 \to X \to 0$ is exact, so $\pi$ is a cokernel of $d_1$. By the universal property of the cokernel, the maps $f$ with $f d_1 = 0$ correspond bijectively to maps $X \to Y$, through $g \mapsto g \pi$. This bijection is additive and natural. $\square$

**Theorem (Long exact sequence in the second variable).** A short exact sequence $0 \to A \to B \to Q \to 0$ gives a long exact sequence
$$0 \to \operatorname{Hom}(X, A) \to \operatorname{Hom}(X, B) \to \operatorname{Hom}(X, Q) \to \operatorname{Ext}^1(X, A) \to \operatorname{Ext}^1(X, B) \to \operatorname{Ext}^1(X, Q) \to \operatorname{Ext}^2(X, A) \to \cdots.$$

*Proof.* Each $P_k$ is projective, so $\operatorname{Hom}(P_k, -)$ is exact. Hence $0 \to \operatorname{Hom}(P, A) \to \operatorname{Hom}(P, B) \to \operatorname{Hom}(P, Q) \to 0$ is a short exact sequence of cochain complexes of abelian groups. Its long exact cohomology sequence (Chapter 2) is the sequence of the theorem, after the identification of $\operatorname{Ext}^0$ with $\operatorname{Hom}$. $\square$

The long exact sequence in the first variable also holds. Its proof needs the horseshoe lemma of Section 2: the horseshoe resolution gives a degreewise split short exact sequence of resolutions, and $\operatorname{Hom}(-, Y)$ keeps it short exact.

**Theorem (Ext detects projectives).** The object $X$ is projective if and only if $\operatorname{Ext}^1(X, Y) = 0$ for every $Y$. In that case $\operatorname{Ext}^n(X, Y) = 0$ for all $n \geq 1$.

*Proof.* If $X$ is projective, $X$ itself, in degree $0$, is a projective resolution. Then $\operatorname{Hom}(P, Y)$ is $\operatorname{Hom}(X, Y)$ in degree $0$, and its cohomology vanishes in positive degrees. Conversely, assume $\operatorname{Ext}^1(X, -) = 0$. Let $p : B \to Q$ be an epimorphism with kernel $A$, and let $f : X \to Q$. The long exact sequence contains $\operatorname{Hom}(X, B) \to \operatorname{Hom}(X, Q) \to \operatorname{Ext}^1(X, A) = 0$. So $f = p g$ for some $g : X \to B$, and $X$ is projective. $\square$

**Lemma (Dimension shifting).** Let $0 \to K \to P \xrightarrow{e} X \to 0$ be exact with $P$ projective. Then $\operatorname{Ext}^{n+1}(X, Y) \cong \operatorname{Ext}^n(K, Y)$ for every $Y$ and every $n \geq 1$.

*Proof.* Let $Q \to K$ be a projective resolution, with augmentation $\varepsilon : Q_0 \to K$. Splice it with $e$: the complex
$$\cdots \to Q_1 \to Q_0 \xrightarrow{\ \iota \varepsilon\ } P \to 0,$$
with $P$ in degree $0$ and $Q_k$ in degree $k + 1$, is a projective resolution of $X$. It is exact at $P$ because the image of $\iota \varepsilon$ is $K = \ker e$, and exact at $Q_0$ because $\iota$ is a monomorphism, so the kernel of $\iota \varepsilon$ is the kernel of $\varepsilon$. In degrees $k \geq 1$ its $\operatorname{Hom}(-, Y)$ complex is $\operatorname{Hom}(Q_{k-1}, Y)$, with the same differentials. The cohomology in degree $n + 1 \geq 2$ only involves the terms in degrees $n$, $n + 1$ and $n + 2$, which are all $\geq 1$. So it equals the cohomology of $\operatorname{Hom}(Q, Y)$ in degree $n$. $\square$

**Corollary (Dimension and syzygies).** With $0 \to K \to P \to X \to 0$ as in the lemma, $\operatorname{pd} X < n + 2$ if and only if $\operatorname{pd} K < n + 1$.

*Proof.* By the lemma, $\operatorname{Ext}^{i+1}(X, -) = 0$ for all $i \geq n + 1$ if and only if $\operatorname{Ext}^i(K, -) = 0$ for all $i \geq n + 1$. $\square$

**Theorem (Projective dimension and resolutions).** For $n \geq 0$, $\operatorname{pd} X \leq n$ if and only if $X$ has a projective resolution $P$ with $P_k = 0$ for $k > n$.

*Proof.* If such a resolution exists, $\operatorname{Hom}(P, Y)$ is zero above degree $n$, so $\operatorname{Ext}^i(X, Y) = 0$ for $i > n$. Conversely, assume $\operatorname{pd} X \leq n$. Take any projective resolution $P$, and let $K_n$ be the kernel of $d_{n-1} : P_{n-1} \to P_{n-2}$, read as the kernel of $\pi$ when $n = 1$, and as $X$ itself when $n = 0$. The truncation $0 \to K_n \to P_{n-1} \to \cdots \to P_0 \to X$ is exact. Apply the corollary $n$ times: $\operatorname{pd} K_n < 1$, so $\operatorname{Ext}^1(K_n, -) = 0$ and $K_n$ is projective by the previous theorem. Then $0 \to K_n \to P_{n-1} \to \cdots \to P_0$ is a projective resolution of length $n$. $\square$

**Proposition (Tor in low degrees).** Let $C$ be as in the definition of Tor. Then $\operatorname{Tor}_n(X, P) = 0$ for $P$ projective and $n \geq 1$. If $X \otimes -$ is right exact, then $\operatorname{Tor}_0(X, Y) \cong X \otimes Y$, and a short exact sequence in $Y$ gives a long exact sequence that ends with $\operatorname{Tor}_1(X, Q) \to X \otimes A \to X \otimes B \to X \otimes Q \to 0$.

*Proof.* These are the vanishing on projectives, the theorem on $L_0$ and the long exact sequence of Section 2, for the functor $X \otimes -$. In $R$-modules over a commutative ring $R$, $X \otimes_R -$ is a left adjoint, with right adjoint $\operatorname{Hom}_R(X, -)$, so it preserves colimits and is right exact. $\square$

The classical *balance* theorem says that $\operatorname{Tor}_n \cong \operatorname{Tor}'_n$: Tor can be computed by resolving either variable. The same holds for Ext, which can be computed by a projective resolution of $X$ or by an injective resolution of $Y$. For Ext, Mathlib obtains balance for free: both descriptions are isomorphisms to the same derived category group, `Projective.Ext` with `ProjectiveResolution.extEquivCohomologyClass` and `Injective.Ext` with `InjectiveResolution.extEquivCohomologyClass`. The index of this edition has no declaration for the isomorphism between `Tor` and `Tor'`.

### Examples

**Example (Ext of $\mathbb{Z}/n$ into $\mathbb{Z}$).** Let $n \geq 1$. The complex $0 \to \mathbb{Z} \xrightarrow{n} \mathbb{Z} \to 0$, in degrees $1$ and $0$, with $\pi : \mathbb{Z} \to \mathbb{Z}/n$, is a projective resolution of $\mathbb{Z}/n$. Apply $\operatorname{Hom}(-, \mathbb{Z})$ and identify $\operatorname{Hom}(\mathbb{Z}, \mathbb{Z}) = \mathbb{Z}$ by $f \mapsto f(1)$. A map $f$ goes to $f \circ n$, so the complex is
$$0 \to \mathbb{Z} \xrightarrow{\ n\ } \mathbb{Z} \to 0$$
in degrees $0$ and $1$. Hence $\operatorname{Ext}^0(\mathbb{Z}/n, \mathbb{Z}) = \ker(n) = 0$, which is $\operatorname{Hom}(\mathbb{Z}/n, \mathbb{Z})$, and
$$\operatorname{Ext}^1(\mathbb{Z}/n, \mathbb{Z}) = \mathbb{Z}/n\mathbb{Z}.$$
In the language of `extMk`, every $f : \mathbb{Z} \to \mathbb{Z}$ in degree $1$ is a cocycle because $P_2 = 0$, and $f$ gives zero exactly when $f(1)$ is a multiple of $n$. The class of $f(1) = 1$ generates the group. It corresponds to the extension $0 \to \mathbb{Z} \xrightarrow{n} \mathbb{Z} \to \mathbb{Z}/n \to 0$. For $n \geq 2$ the group is not zero, so $\mathbb{Z}/n$ is not projective, and its projective dimension is exactly $1$.

**Example (Ext by an injective resolution).** Compute the same group with the injective resolution $0 \to \mathbb{Z} \to \mathbb{Q} \to \mathbb{Q}/\mathbb{Z} \to 0$ of the second variable. Then $\operatorname{Hom}(\mathbb{Z}/n, \mathbb{Q}) = 0$, and $\operatorname{Hom}(\mathbb{Z}/n, \mathbb{Q}/\mathbb{Z})$ is the group of elements of order dividing $n$, cyclic of order $n$, generated by $\tfrac1n$. So $\operatorname{Ext}^1(\mathbb{Z}/n, \mathbb{Z}) \cong \mathbb{Z}/n$ again. For $n = 2$ this is the group $R^1 F(\mathbb{Z})$ of Section 2. The two answers agree, as balance says.

**Example (Ext between cyclic groups).** Resolve $\mathbb{Z}/m$ by $\mathbb{Z} \xrightarrow{m} \mathbb{Z}$ and apply $\operatorname{Hom}(-, \mathbb{Z}/n)$. The complex is $\mathbb{Z}/n \xrightarrow{m} \mathbb{Z}/n$. Its kernel and cokernel both have order $d = \gcd(m, n)$, and both are cyclic, so
$$\operatorname{Hom}(\mathbb{Z}/m, \mathbb{Z}/n) \cong \operatorname{Ext}^1(\mathbb{Z}/m, \mathbb{Z}/n) \cong \mathbb{Z}/d.$$
For $m = n = p$ prime, the nonzero classes in $\operatorname{Ext}^1(\mathbb{Z}/p, \mathbb{Z}/p)$ correspond to the extension $0 \to \mathbb{Z}/p \to \mathbb{Z}/p^2 \to \mathbb{Z}/p \to 0$ up to automorphisms of the ends.

**Example (Tor of cyclic groups).** Resolve $\mathbb{Z}/n$ by $\mathbb{Z} \xrightarrow{n} \mathbb{Z}$ and apply $\mathbb{Z}/m \otimes -$. The complex is $\mathbb{Z}/m \xrightarrow{n} \mathbb{Z}/m$ in degrees $1$ and $0$. The kernel of multiplication by $n$ on $\mathbb{Z}/m$ is the subgroup generated by $m/d$, of order $d = \gcd(m, n)$. The cokernel is $\mathbb{Z}/(m, n) = \mathbb{Z}/d$. So
$$\operatorname{Tor}_1(\mathbb{Z}/m, \mathbb{Z}/n) \cong \mathbb{Z}/d, \qquad \operatorname{Tor}_0(\mathbb{Z}/m, \mathbb{Z}/n) \cong \mathbb{Z}/m \otimes \mathbb{Z}/n \cong \mathbb{Z}/d,$$
and $\operatorname{Tor}_k = 0$ for $k \geq 2$. For $m = n = 2$, $\operatorname{Tor}_1$ is the kernel of $\mathbb{Z}/2 \otimes (\mathbb{Z} \xrightarrow{2} \mathbb{Z})$, the map that Section 2 found to be zero.

**Example (Infinite projective dimension).** Over $R = \mathbb{Z}/4$, the module $\mathbb{Z}/2$ has the periodic resolution $\cdots \xrightarrow{2} R \xrightarrow{2} R \to \mathbb{Z}/2$ of Section 1. Apply $\operatorname{Hom}_R(-, \mathbb{Z}/2)$. Each term is $\operatorname{Hom}_R(R, \mathbb{Z}/2) = \mathbb{Z}/2$, and each map is multiplication by $2$, which is zero on $\mathbb{Z}/2$. So $\operatorname{Ext}^n_R(\mathbb{Z}/2, \mathbb{Z}/2) = \mathbb{Z}/2$ for every $n$, and $\operatorname{pd} \mathbb{Z}/2 = \infty$. This was promised in Section 1.

**Example (Injective dimension of $\mathbb{Z}$).** The resolution $\mathbb{Z} \to \mathbb{Q} \to \mathbb{Q}/\mathbb{Z}$ has length $1$, so $\operatorname{Ext}^i(X, \mathbb{Z}) = 0$ for $i \geq 2$ and all $X$. Since $\operatorname{Ext}^1(\mathbb{Z}/2, \mathbb{Z}) \ne 0$, the injective dimension of $\mathbb{Z}$ is $1$. Every abelian group has projective and injective dimension at most $1$, because subgroups of free groups are free and quotients of divisible groups are divisible.

### The library around it

::: mathlib
`CategoryTheory.Tor` · `Mathlib.CategoryTheory.Monoidal.Tor`

For a monoidal abelian category `C` with `[MonoidalPreadditive C]` and `[HasProjectiveResolutions C]`, `Tor C n : C ⥤ C ⥤ C` sends `X` to `Functor.leftDerived ((tensoringLeft C).obj X) n`. `Tor' C n` derives `tensoringRight` instead. `isZero_Tor_succ_of_projective` and `isZero_Tor'_succ_of_projective` are the only theorems of the file. The values lie in `C`, not in abelian groups: for `ModuleCat R` over a commutative ring they are modules.

<?decl CategoryTheory.Tor?>
:::

::: mathlib
`CategoryTheory.HasProjectiveDimensionLT` · `Mathlib.CategoryTheory.Abelian.Projective.Dimension`

The class `HasProjectiveDimensionLT X n` says that `Ext X Y i` is a subsingleton for all `Y` and `i ≥ n`. `HasProjectiveDimensionLE X n` abbreviates `HasProjectiveDimensionLT X (n + 1)`. `projectiveDimension X : WithBot ℕ∞` is the infimum, with `projectiveDimension_le_iff` and `projectiveDimension_eq_zero_iff`. `projective_iff_subsingleton_ext_one` is the theorem that Ext detects projectives. `ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff` is the corollary on syzygies, stated for a short exact `S` with `S.X₂` projective.

<?decl CategoryTheory.HasProjectiveDimensionLT?>
:::

The injective file has the dual names: `HasInjectiveDimensionLT`, `HasInjectiveDimensionLE`, `injectiveDimension`, `injective_iff_subsingleton_ext_one`, `injectiveDimension_le_iff` and the `ShortExact` lemmas. The index of this edition has no declaration for the theorem that the projective dimension is the minimal length of a projective resolution.

::: mathlib
`CategoryTheory.InjectiveResolution.extMk` · `Mathlib.CategoryTheory.Abelian.Injective.Ext`

For `R : InjectiveResolution Y`, a map `f : X ⟶ R.cocomplex.X n` with `f ≫ R.cocomplex.d n m = 0` gives a class in `Ext X Y n`. The lemmas `extMk_surjective` and `extMk_eq_zero_iff` mirror the projective ones.

<?decl CategoryTheory.InjectiveResolution.extMk?>
:::

::: mathlib
`CategoryTheory.Abelian.Ext` · `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`

The derived category Ext, `Ext X Y n : Type w`, under `[HasExt.{w} C]`. Chapter 5 defines it. The older `Ext R C n : Cᵒᵖ ⥤ C ⥤ ModuleCat R` in `Mathlib.CategoryTheory.Abelian.Ext`, the left derived functor of `linearYoneda` in the first variable, is deprecated since 2026-10-25, together with `ProjectiveResolution.isoExt`. New code uses `Abelian.Ext`.

<?decl CategoryTheory.Abelian.Ext?>
:::

Common errors of a learner:

- $\operatorname{Ext}^n(X, Y)$ is contravariant in $X$. The resolution is of the first variable when it is projective, and of the second when it is injective.
- The augmentation is not part of $\operatorname{Hom}(P, Y)$. Including $\operatorname{Hom}(X, Y)$ in degree $-1$ makes the complex exact in degree $0$ and loses $\operatorname{Ext}^0$.
- `Tor C n` derives in the second variable. A computation that resolves the first variable is about `Tor'`, and the comparison is not in the library.
- `projectiveDimension X = 0` needs `X` nonzero. The zero object has projective dimension `⊥`.

### Exercises

1. (A) Compute $\operatorname{Ext}^n(\mathbb{Z}/6, \mathbb{Z}/4)$ and $\operatorname{Tor}_n(\mathbb{Z}/6, \mathbb{Z}/4)$ for all $n$.
2. (A) Show that $\operatorname{Tor}_1(\mathbb{Z}/n, A)$ is the $n$-torsion subgroup $A[n]$ for every abelian group $A$.
3. (B) Show that $\operatorname{Ext}^1(X, Y_1 \oplus Y_2) \cong \operatorname{Ext}^1(X, Y_1) \oplus \operatorname{Ext}^1(X, Y_2)$, and deduce $\operatorname{Ext}^1(A, \mathbb{Z})$ for every finite abelian group $A$.
4. (B) Prove that $Y$ is injective if and only if $\operatorname{Ext}^1(X, Y) = 0$ for all $X$, using the long exact sequence in the first variable.
5. (B) Show that $\operatorname{Ext}^1(\mathbb{Q}, \mathbb{Z}) \ne 0$. *Hint:* use $0 \to \mathbb{Z} \to \mathbb{Q} \to \mathbb{Q}/\mathbb{Z} \to 0$ and the long exact sequence in the second variable with $X = \mathbb{Q}$.
6. (C) Let $k$ be a field and $R = k[x, y]$. Use the Koszul resolution of Section 1 to compute $\operatorname{Ext}^n_R(k, k)$ and $\operatorname{Tor}^R_n(k, k)$, and conclude $\operatorname{pd}_R k = 2$.
7. (C) For a short exact sequence $0 \to A \to B \to Q \to 0$, prove $\operatorname{pd} B \leq \max(\operatorname{pd} A, \operatorname{pd} Q)$ and $\operatorname{pd} A \leq \max(\operatorname{pd} B, \operatorname{pd} Q - 1)$. *Hint:* the long exact sequence in the first variable.

### Notes and history

Ext appeared in algebraic topology, in the universal coefficient theorem, and Eilenberg and MacLane named it in 1942 in their study of group extensions, which $\operatorname{Ext}^1$ classifies. Tor arose from the Künneth formula. Cartan and Eilenberg (1956) treated both as derived functors and proved balance. Hilbert's syzygy theorem says that the global dimension of $k[x_1, \ldots, x_n]$ is $n$; Serre characterized regular local rings by finite global dimension.

The Mathlib Authors include Kim Morrison and Adam Topaz for the older `Abelian.Ext` file and Kim Morrison for `Monoidal.Tor`. Joël Riou wrote `Projective.Ext` and `Injective.Ext`, Joël Riou and Nailin Guan wrote `Projective.Dimension`, and Nailin Guan wrote `Injective.Dimension`.

### Reference

<?reference?>
