---
title: Perfections, tilts and Fontaine's theta map
kind: api
modules:
  - Mathlib.RingTheory.Perfection
  - Mathlib.RingTheory.Teichmuller
  - Mathlib.RingTheory.Perfectoid.Untilt
  - Mathlib.RingTheory.Perfectoid.FontaineTheta
  - Mathlib.RingTheory.Perfectoid.BDeRham
explains:
  E2: [Perfection, Perfection.coeff, Perfection.lift, PerfectionMap, PreTilt, Perfection.teichmuller, PreTilt.untilt, WittVector.fontaineTheta, WittVector.fontaineTheta_teichmuller, BDeRhamPlus]
  E1: auto
families: []
requires: [V10.C03, V10.C06, V10.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Perfections, tilts and Fontaine's theta map

### Overview

A ring $R$ of characteristic $p$ is perfect if its Frobenius $x \mapsto x^p$ is bijective. Each ring of characteristic $p$ has a universal perfect ring that maps to it, its perfection. It is the inverse limit of the system $\cdots \to R \to R \to R$ in which each map is the Frobenius. An element is a sequence $(x_0, x_1, \dots)$ with $x_{n+1}^p = x_n$.

Let $O$ be a ring that is complete for the $p$-adic topology, for example the ring of integers of $\mathbb{C}_p$. The tilt of $O$ is the perfection of $O/p$, a perfect ring of characteristic $p$. Two maps connect $O$ with its tilt $O^\flat$.

1. The untilt $x \mapsto x^\sharp$ is a multiplicative map $O^\flat \to O$ that lifts the zeroth coordinate. It is not additive.
2. Fontaine's map $\theta : W(O^\flat) \to O$ is a ring map with $\theta([x]) = x^\sharp$. It is surjective when the Frobenius of $O/p$ is surjective.

These are the first objects of $p$-adic Hodge theory. Mathlib also defines the period rings $B_{\mathrm{dR}}^+$ and $B_{\mathrm{dR}}$ from $\theta$.

### The library around it

#### The perfection

The module `Mathlib.RingTheory.Perfection` defines `Perfection R p`. It is the subring `Perfection.subring` of sequences $f : \mathbb{N} \to R$ with $f(n + 1)^p = f(n)$. The ring maps `Perfection.coeff R p n` give the coordinates, and `Perfection.coeff_mk` computes them. The perfection is perfect, by the instance `Perfection.instPerfectRing`. Its Frobenius shifts the coordinates, `Perfection.coeff_iterate_frobenius`, and its inverse is `Perfection.pthRoot`.

**Theorem.** Let $P$ be perfect of characteristic $p$ and $S$ of characteristic $p$. Composition with the zeroth coordinate is a bijection from ring maps $P \to \operatorname{Perf}(S)$ to ring maps $P \to S$.

This is `Perfection.lift`. A map $f : P \to S$ lifts to $r \mapsto (f(r), f(r^{1/p}), f(r^{1/p^2}), \dots)$. The functoriality is `Perfection.map`, with `Perfection.coeff_map`. If the Frobenius of $R$ is surjective, then each coordinate map is surjective, `Perfection.coeff_surjective`.

The predicate `PerfectionMap p π` says that $\pi : P \to R$ has the same universal property as the zeroth coordinate. It has fields for injectivity and surjectivity on compatible sequences of $p$-th roots. The basic examples are `PerfectionMap.of` for the zeroth coordinate and `PerfectionMap.id` for a perfect ring. Each perfection map gives a ring isomorphism `PerfectionMap.equiv` with the perfection, and `PerfectionMap.lift` is the universal property.

For a monoid, `Perfection M p` is a monoid, with coordinates `Perfection.coeffMonoidHom`. This is needed for the untilt, which is only multiplicative.

#### The tilt

For a ring $O$, the quotient $O/p$ is `ModP O p`, and `PreTilt O p` is `Perfection (ModP O p) p`. Now let $K$ be a field with a valuation $v$ and ring of integers $O$, the setting of `Valuation.Integers` from Chapter 3. Then `PreTilt O p` is a domain, `PreTilt.isDomain`, and it has a valuation `PreTilt.val`. For $f \ne 0$, its value is $\operatorname{preVal}(f_n)^{p^n}$ for each $n$ with $f_n \ne 0$, where `ModP.preVal` is the valuation of a lift of $f_n$ to $O$. The tilt `Tilt K v O hv p` is the fraction field of the pre-tilt, a field of characteristic $p$.

#### Teichmüller lifts to a complete ring

The module `Mathlib.RingTheory.Teichmuller` works with a ring $R$ that is complete for an ideal $I$, with $R/I$ of characteristic $p$.

**Theorem.** There is a unique multiplicative map $[\cdot] : \operatorname{Perf}(R/I) \to R$ such that $[x]$ reduces to $x_0$ modulo $I$. If $y \in R$ lifts $x_n$, then $[x] \equiv y^{p^n}$ modulo $I^{n+1}$.

The map is `Perfection.teichmuller p I`. The congruence is `Perfection.teichmuller_sModEq`. The characterization `Perfection.teichmuller_spec` says that an element with these congruences for all large $n$ is $[x]$. The version that also preserves $0$ is `Perfection.teichmuller₀`.

*Proof sketch.* Let $y_n$ lift $x_n$. Then $y_{n+1}^p \equiv y_n$ modulo $I$. Since $p \in I$, this gives $y_{n+1}^{p^{n+1}} \equiv y_n^{p^n}$ modulo $I^{n+1}$. So the sequence $y_n^{p^n}$ is Cauchy for the $I$-adic topology, `Perfection.teichmullerCauchy`. Its limit does not depend on the lifts, and it is multiplicative. $\square$

As a consequence, `Perfection.quotientMulEquiv` is a monoid isomorphism between `Perfection R p` and `Perfection (R ⧸ I) p`.

#### The untilt

The module `Mathlib.RingTheory.Perfectoid.Untilt` applies this to $I = (p)$. For a $p$-adically complete ring $O$ in which $p$ is not a unit, `PreTilt.untilt : PreTilt O p →* O` is the map $x \mapsto x^\sharp$. Its reduction modulo $p$ is the zeroth coordinate, `PreTilt.mk_untilt_eq_coeff_zero`. The power rule `PreTilt.untilt_iterate_frobeniusEquiv_symm_pow` says that $(x^{1/p^n})^\sharp$ is a $p^n$-th root of $x^\sharp$.

**Example.** Let $O = \mathcal{O}_{\mathbb{C}_p}$. Choose a compatible system of roots $p, p^{1/p}, p^{1/p^2}, \dots$ in $O$. Their images in $O/p$ form an element $p^\flat$ of $O^\flat$, and $(p^\flat)^\sharp = p$. The element $[p^\flat] - p$ of $W(O^\flat)$ lies in the kernel of $\theta$, and a classical theorem says that it generates the kernel.

#### Fontaine's theta map

The module `Mathlib.RingTheory.Perfectoid.FontaineTheta` constructs $\theta$ for a $p$-adically complete ring $R$. It does not need $R$ to be perfectoid.

**Theorem.** There is a ring map $\theta : W(R^\flat) \to R$ with $\theta([x]) = x^\sharp$ for each $x \in R^\flat$.

This is `WittVector.fontaineTheta`, with `WittVector.fontaineTheta_teichmuller`.

*Construction.* The $n$-th ghost component $W(R) \to R$ becomes a ring map $W(R/p) \to R/p^{n+1}$ after reduction. The reason is that a change of the coordinates by multiples of $p$ changes $w_n$ by a multiple of $p^{n+1}$, `WittVector.ker_map_le_ker_mk_comp_ghostComponent`. The resulting map is `WittVector.ghostComponentModPPow`. Then $\theta_n$ is the composite
$$W(R^\flat) \xrightarrow{W(F^{-n})} W(R^\flat) \to W(R/p) \to R/p^{n+1},$$
where the middle map takes the zeroth coordinate. This is `WittVector.fontaineThetaModPPow`. The maps $\theta_n$ are compatible, `WittVector.factorPowSucc_comp_fontaineThetaModPPow`. Since $R$ is $p$-adically complete, they define $\theta$. $\square$

If the Frobenius of $R/p$ is surjective, then $\theta$ is surjective, `surjective_fontaineTheta`. Modulo $p$, $\theta(x)$ is the zeroth coordinate of $x_0$, `WittVector.mk_fontaineTheta`.

#### Period rings

The module `Mathlib.RingTheory.Perfectoid.BDeRham` defines two rings for a $p$-adically complete ring $R$. The map `fontaineThetaInvertP` is $\theta$ with $p$ inverted on both sides.

1. `BDeRhamPlus R p` is the completion of $W(R^\flat)[1/p]$ for the kernel of this map. It uses `AdicCompletion` from Chapter 6.
2. `BDeRham R p` is the localization of `BDeRhamPlus R p` at the generators of the kernel.

For $R = \mathcal{O}_{\mathbb{C}_p}$, `PadicComplexInt`, these are the classical rings $B_{\mathrm{dR}}^+$ and $B_{\mathrm{dR}}$ of Fontaine. The library does not yet prove that $B_{\mathrm{dR}}^+$ is a DVR.

#### Common errors

1. `PreTilt.untilt` and `Perfection.teichmuller` are `MonoidHom`s. In general $(x + y)^\sharp \ne x^\sharp + y^\sharp$.
2. `WittVector.fontaineTheta` needs `IsAdicComplete (Ideal.span {(p : R)}) R` and the fact that $p$ is not a unit. If $p = 0$ in $R$, then `BDeRhamPlus R p` is the zero ring.
3. `Perfection R p` for a ring that is not of characteristic $p$ is only a monoid in general. The ring structure needs `CharP R p`, and the version for the $p$-adic ring itself goes through `Perfection.quotientMulEquiv`.

### Exercises

1. (A) Show that the perfection of a perfect ring $R$ is isomorphic to $R$, with `PerfectionMap.id`.
2. (A) Show that the perfection of $\mathbb{F}_p[t]$ is $\mathbb{F}_p$, by a computation of compatible sequences of $p$-th roots.
3. (B) Show that the perfection of $\mathbb{F}_p[t]/(t^p)$ is $\mathbb{F}_p$, but the perfection of $\mathbb{F}_p[t^{1/p^\infty}]/(t)$ is the $t$-adic completion of $\mathbb{F}_p[t^{1/p^\infty}]$.
4. (B) Prove the congruence $y_{n+1}^{p^{n+1}} \equiv y_n^{p^n}$ modulo $I^{n+1}$ used in the Teichmüller construction.
5. (B) Let $O = \mathbb{Z}_p$. Show that $O^\flat = \mathbb{F}_p$, and that $\theta : W(\mathbb{F}_p) \to \mathbb{Z}_p$ is the isomorphism of Chapter 8.
6. (C) Show that the Teichmüller map $\operatorname{Perf}(\mathbb{F}_p) \to \mathbb{Z}_p$ sends $a$ to the unique $(p-1)$-th root of unity that reduces to $a$, for $a \ne 0$.

### Reference

<?reference?>
