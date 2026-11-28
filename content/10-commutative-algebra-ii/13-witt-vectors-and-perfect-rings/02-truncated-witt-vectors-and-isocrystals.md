---
title: Truncated Witt vectors, completeness and isocrystals
kind: api
modules:
  - Mathlib.RingTheory.WittVector.Truncated
  - Mathlib.RingTheory.WittVector.Complete
  - Mathlib.RingTheory.WittVector.Domain
  - Mathlib.RingTheory.WittVector.FrobeniusFractionField
  - Mathlib.RingTheory.WittVector.Isocrystal
explains:
  E2: [TruncatedWittVector, WittVector.truncate, WittVector.lift, WittVector.quotientPEquiv, WittVector.isAdicCompleteIdealSpanP, WittVector.verschiebung_nonzero, WittVector.frobeniusRotation, WittVector.exists_frobenius_solution_fractionRing, WittVector.Isocrystal, WittVector.isocrystal_classification]
  E1: auto
families: []
requires: [V10.C06, V10.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Truncated Witt vectors, completeness and isocrystals

### Overview

The ring $W(R)$ is an inverse limit of rings $W_n(R)$ of truncated Witt vectors. An element of $W_n(R)$ is a list $(x_0, \dots, x_{n-1})$, and the ring operations are the first $n$ structure polynomials. For $R = \mathbb{F}_p$, the ring $W_n(\mathbb{F}_p)$ is $\mathbb{Z}/p^n$, and the inverse limit is $\mathbb{Z}_p$.

For a perfect ring $k$ of characteristic $p$, the kernel of $W(k) \to W_n(k)$ is the ideal $p^nW(k)$. So $W(k)$ is complete for the $p$-adic topology, and $W(k)/p \cong k$. If $k$ is a domain, then $W(k)$ is a domain.

The last part of this section treats a theorem of Dieudonné theory. Let $k$ be an algebraically closed field of characteristic $p$, let $K$ be the fraction field of $W(k)$, and let $\varphi$ be the Frobenius of $K$. An isocrystal is a finite dimensional $K$-vector space $V$ with a $\varphi$-semilinear bijection $\Phi : V \to V$. Mathlib proves that each isocrystal of dimension $1$ is isomorphic to the standard one $K$ with $\Phi(x) = p^m\varphi(x)$, for a unique integer slope $m$.

### The library around it

#### Truncated Witt vectors

The type `TruncatedWittVector p n R` in `Mathlib.RingTheory.WittVector.Truncated` is the type of functions `Fin n → R`. The constructor is `TruncatedWittVector.mk`, and the coordinates are `TruncatedWittVector.coeff`. The ring map `WittVector.truncate n : 𝕎 R →+* TruncatedWittVector p n R` forgets all coordinates from position $n$ on. It is surjective, `WittVector.truncate_surjective`, and the ring structure on `TruncatedWittVector p n R` is the one that makes it a ring map. Its kernel is described by `WittVector.mem_ker_truncate`: $x$ maps to $0$ if and only if $x_i = 0$ for $i < n$.

For $n \le m$, `TruncatedWittVector.truncate` gives the transition map $W_m(R) \to W_n(R)$, and `TruncatedWittVector.truncate_comp_wittVector_truncate` says that the maps are compatible. Over a finite ring, `TruncatedWittVector.card` gives $|W_n(R)| = |R|^n$.

**Theorem.** $W(R)$ is the inverse limit of the rings $W_n(R)$. A compatible family of ring maps $f_n : S \to W_n(R)$ comes from a unique ring map $S \to W(R)$.

The map is `WittVector.lift`, and the bijection between compatible families and ring maps is `WittVector.liftEquiv`. The equation `WittVector.truncate_lift` says that the truncations of the lift are the given maps. Injectivity comes from `TruncatedWittVector.iInf_ker_truncate`: the kernels of all truncations meet in $0$. For $R = \mathbb{Z}/p$, the ring isomorphism $\mathbb{Z}/p^n \cong W_n(\mathbb{Z}/p)$ is `TruncatedWittVector.zmodEquivTrunc`, and the lift of these maps gives the isomorphism with $\mathbb{Z}_p$ of Chapter 8.

#### Completeness

The module `Mathlib.RingTheory.WittVector.Complete` works over a perfect ring $k$ of characteristic $p$.

**Theorem.** An element $x$ of $W(k)$ lies in $p^nW(k)$ if and only if $x_i = 0$ for $i < n$.

This is `WittVector.mem_span_p_pow_iff_le_coeff_eq_zero`.

*Proof.* In characteristic $p$, $px = V(F(x))$. Since $k$ is perfect, $F$ is bijective, so $pW(k) = V(W(k))$. The image of $V$ is the set of Witt vectors with $x_0 = 0$. By induction, $p^nW(k)$ is the image of $V^n$, the set of Witt vectors whose first $n$ coordinates are $0$. $\square$

Three consequences follow.

1. The kernel of the zeroth coordinate is $(p)$, `WittVector.ker_constantCoeff`, so $W(k)/(p) \cong k$. The isomorphism is `WittVector.quotientPEquiv`.
2. The ideals $p^nW(k)$ are the kernels of the truncations. So the $p$-adic topology is the inverse limit topology, and $W(k)$ is $p$-adically complete and separated. This is the instance `WittVector.isAdicCompleteIdealSpanP` of `IsAdicComplete` from Chapter 6.
3. Two Witt vectors agree in the first $n$ coordinates if and only if their difference does, `WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero`. Note that this is not obvious, since subtraction mixes the coordinates.

#### Witt vectors of a domain

The module `Mathlib.RingTheory.WittVector.Domain` proves that $W(R)$ is a domain when $R$ is a domain of characteristic $p$, the instance `WittVector.instIsDomain`. The proof does not need $R$ to be perfect.

*Proof sketch.* Each nonzero $x$ has the form $V^n(x')$ with $x'_0 \ne 0$, by `WittVector.verschiebung_nonzero`. Here $n$ is the number of leading zero coordinates, and $x'$ is the shift `WittVector.shift`. For $x = V^m(a)$ and $y = V^n(b)$, `WittVector.iterate_verschiebung_mul_coeff` gives the coordinate of $xy$ at $m + n$ as $a_0^{p^n}b_0^{p^m}$. This is nonzero in a domain, so $xy \ne 0$. $\square$

Together with the DVR theorem of Chapter 8, this gives the standard picture: for a perfect field $k$, $W(k)$ is a complete DVR with uniformizer $p$ and residue field $k$.

#### The Frobenius on the fraction field

Let $k$ be an algebraically closed field of characteristic $p$. The module `Mathlib.RingTheory.WittVector.FrobeniusFractionField` solves the equation $\varphi(b)a = p^mb$ in the fraction field of $W(k)$.

**Theorem.** Let $a_1, a_2 \in W(k)$ with nonzero zeroth coordinates. There is a nonzero $b \in W(k)$ with $F(b)a_1 = ba_2$.

The element is `WittVector.frobeniusRotation`, and the equation is `WittVector.frobenius_frobeniusRotation`. The coordinates of $b$ are found one at a time. The zeroth coordinate solves $b_0^{p-1} = a_{2,0}/a_{1,0}$, `WittVector.RecursionBase.solution_spec`. For the coordinate $n + 1$, the product formula `WittVector.nth_mul_coeff` of Section 1 gives a polynomial equation of degree $p$ in $b_{n+1}$, `WittVector.RecursionMain.succNthDefiningPoly_degree`. A root exists because $k$ is algebraically closed, `WittVector.RecursionMain.root_exists`.

**Corollary.** Each nonzero $a$ in the fraction field $K$ of $W(k)$ has a nonzero $b \in K$ and an integer $m$ with $\varphi(b)a = p^mb$. This is `WittVector.exists_frobenius_solution_fractionRing`.

To prove it, write $a = p^m u_1/u_2$ with $u_1, u_2$ of nonzero zeroth coordinate and apply the theorem. The Frobenius of $K$ is `WittVector.FractionRing.frobenius`, the extension of `WittVector.frobeniusEquiv` to fractions.

#### Isocrystals

The module `Mathlib.RingTheory.WittVector.Isocrystal` defines the class `WittVector.Isocrystal p k V`, for a vector space $V$ over $K$ with a $\varphi$-semilinear equivalence `WittVector.Isocrystal.frobenius`. Maps of isocrystals are `WittVector.IsocrystalHom` and `WittVector.IsocrystalEquiv`. They are linear maps that commute with $\Phi$, by `WittVector.IsocrystalHom.frob_equivariant`. The standard isocrystal of slope $m$ is `WittVector.StandardOneDimIsocrystal p k m`, the field $K$ with $\Phi(x) = p^m\varphi(x)$, `WittVector.StandardOneDimIsocrystal.frobenius_apply`.

**Theorem.** Let $k$ be algebraically closed and let $V$ be an isocrystal of dimension $1$. Then $V$ is isomorphic to the standard isocrystal of slope $m$ for some $m \in \mathbb{Z}$.

This is `WittVector.isocrystal_classification`.

*Proof.* Choose a basis vector $x$. Then $\Phi(x) = ax$ with $a \ne 0$. By the corollary, there are $b \ne 0$ and $m$ with $\varphi(b)a = p^mb$. Put $y = bx$. Then $\Phi(y) = \varphi(b)ax = p^my$. The map $c \mapsto cy$ from $K$ to $V$ is linear and bijective, and $\Phi(cy) = \varphi(c)p^my$. So it is an isomorphism of isocrystals. $\square$

#### Common errors

1. The completeness results need `PerfectRing k p`. For a ring that is not perfect, $pW(R)$ is smaller than the image of $V$, and the kernel of the zeroth coordinate is not $(p)$.
2. `TruncatedWittVector p n R` has the coordinates $0, \dots, n - 1$. So `WittVector.truncate n` corresponds to the quotient by $p^n$, not by $p^{n+1}$.
3. `WittVector.isocrystal_classification` needs `IsAlgClosed k` and `Module.finrank` equal to $1$. Over $\mathbb{F}_p$ the equation $b_0^{p-1} = c$ need not have a root.

### Exercises

1. (A) Show that $W_1(R) \cong R$ as rings, and describe the transition map $W_2(R) \to W_1(R)$.
2. (A) Use `TruncatedWittVector.card` to count the elements of $W_3(\mathbb{F}_4)$.
3. (B) Show that $W_2(\mathbb{F}_p) \cong \mathbb{Z}/p^2$ by an explicit check of the addition rule $(a_0, a_1) + (b_0, b_1) = (a_0 + b_0, a_1 + b_1 - \sum_{0 < i < p} \frac{1}{p}\binom{p}{i}a_0^ib_0^{p-i})$.
4. (B) Show that $W(\mathbb{F}_p[t])$ is a domain, and show that $p$ does not generate the kernel of its zeroth coordinate.
5. (B) Show that two standard isocrystals of slopes $m$ and $m'$ are isomorphic only if $m = m'$. Use the valuation of $K$.
6. (C) Prove `WittVector.mem_span_p_pow_iff_le_coeff_eq_zero` in detail from the identities of Section 1.

### Reference

<?reference?>
