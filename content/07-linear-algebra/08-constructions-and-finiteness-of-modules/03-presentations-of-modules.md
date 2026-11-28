---
title: Presentations and finitely presented modules
kind: api
modules:
  - Mathlib.Algebra.Module.Presentation.Basic
  - Mathlib.Algebra.Module.Presentation.Cokernel
  - Mathlib.Algebra.Module.Presentation.Differentials
  - Mathlib.Algebra.Module.Presentation.DirectSum
  - Mathlib.Algebra.Module.Presentation.Finite
  - Mathlib.Algebra.Module.Presentation.Free
  - Mathlib.Algebra.Module.Presentation.RestrictScalars
  - Mathlib.Algebra.Module.Presentation.Tautological
  - Mathlib.Algebra.Module.Presentation.Tensor
  - Mathlib.Algebra.Module.FinitePresentation
explains:
  E2: [Module.Relations, Module.Relations.Solution.IsPresentation, Module.Relations.Solution.isPresentation_iff, Module.Presentation, Module.Presentation.cokernel, Module.free_iff_exists_presentation, Module.FinitePresentation, Module.finitePresentation_iff_exists_presentation, Module.FinitePresentation.fg_ker, Module.finitePresentation_iff_finite]
  E1: auto
families: []
requires: [V05, V06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Presentations and finitely presented modules

### Overview

A presentation of a module $M$ over a ring $A$ gives $M$ by generators and relations. There is a set $G$ of generators and a set $R$ of relations, and each relation is a linear combination of the generators with coefficients in $A$. The module is then the quotient $A^{(G)} / K$, where $A^{(G)}$ is the free module on $G$ and $K$ is the submodule spanned by the relations. A module is finitely presented if it has a presentation with $G$ and $R$ finite. Over a Noetherian ring each finitely generated module is finitely presented, but over other rings the two conditions are different. This section covers the data of a presentation in Mathlib, the presentations of standard constructions, and the class `Module.FinitePresentation` with its behaviour in exact sequences and under localization.

### The library around it

#### Relations and solutions

A term of `Module.Relations A` is the shape of a presentation. It has a type `Module.Relations.G` of generators, a type `Module.Relations.R` of relations, and for each $r$ the element `Module.Relations.relation r` of $G \to_0 A$, the coefficients of the relation. The linear map `Module.Relations.map` sends $A^{(R)}$ to $A^{(G)}$, and the module defined by the relations is `Module.Relations.Quotient`, the quotient of $A^{(G)}$ by the span of the relations (`Module.Relations.ker_toQuotient`). The ring must be a ring and not a semiring, since the quotient uses a submodule.

A solution of the relations in a module $M$, `Module.Relations.Solution M`, is a family `Module.Relations.Solution.var` of elements of $M$, one for each generator, such that each relation holds in $M$. It is the same as a linear map $\pi : A^{(G)} \to M$ that kills each relation, `Module.Relations.Solution.π`. A linear map $f : M \to N$ sends a solution in $M$ to a solution in $N$, `Module.Relations.Solution.postcomp f`. Each solution gives a map `Module.Relations.Solution.fromQuotient` from the quotient to $M$.

A solution is a presentation of $M$, `Module.Relations.Solution.IsPresentation`, when it is universal: for each solution $s$ in a module $N$ there is a unique linear map $M \to N$ that sends the given solution to $s$. The map is `Module.Relations.Solution.IsPresentation.desc`, and `Module.Relations.Solution.IsPresentation.linearMapEquiv` states that the linear maps $M \to N$ are in bijection with the solutions in $N$. Two presentations with the same relations give equivalent modules, `Module.Relations.Solution.IsPresentation.uniq`.

**Theorem.** A solution with variables $v_g \in M$ is a presentation if and only if the $v_g$ span $M$ and the kernel of $\pi : A^{(G)} \to M$ is the span of the relations.

*Proof.* If the two conditions hold, then $\pi$ induces an equivalence from $A^{(G)} / K$ to $M$, where $K$ is the span of the relations. A linear map from $A^{(G)} / K$ to $N$ is the same as a linear map from $A^{(G)}$ that kills $K$, and this is a solution in $N$. So the solution is universal. Conversely, the quotient `Module.Relations.Quotient` has a universal solution (`Module.Relations.Solution.ofQuotient_isPresentation`), and two universal solutions are equivalent by a map that respects the variables. So $M$ is equivalent to $A^{(G)} / K$ by a map over $\pi$, and the two conditions hold. $\square$

This is `Module.Relations.Solution.isPresentation_iff`, and `Module.Relations.Solution.isPresentation_mk` is the direction that builds a presentation. The equivalence with the quotient is `Module.Relations.Solution.IsPresentation.linearEquiv`. A presentation also gives the exact sequence $A^{(R)} \to A^{(G)} \to M \to 0$ (`Module.Relations.Solution.IsPresentation.exact`).

The structure `Module.Presentation A M` puts the relations, the solution and the proof together. The constructor from a proof is `Module.Presentation.ofIsPresentation`, and `Module.Presentation.ofLinearEquiv` moves a presentation along a linear equivalence.

#### Presentations of constructions

Each module has a presentation, `Module.Presentation.tautological`: there is a generator $[m]$ for each $m \in M$, and the relations are $[m_1] + [m_2] = [m_1 + m_2]$ and $a [m] = [a m]$. It is large, but it shows that presentations exist. The other constructions are:

| Module | Presentation |
|---|---|
| a free module $G \to_0 A$ | `Module.presentationFinsupp`, with no relations |
| a cokernel $M_2 / f(M_1)$ | `Module.Presentation.cokernel` |
| the end of an exact sequence $M_1 \to M_2 \to M_3 \to 0$ | `Module.Presentation.ofExact` |
| a direct sum $\bigoplus_i M_i$ | `Module.Presentation.directSum` |
| $\iota \to_0 N$ | `Module.Presentation.finsupp` |
| a tensor product $M_1 \otimes M_2$ | `Module.Presentation.tensor` |
| a $B$-module as an $A$-module | `Module.Presentation.restrictScalars` |
| the differentials $\Omega_{S/R}$ | `Algebra.Presentation.differentials` |

The cokernel needs a presentation of $M_2$, a family of generators of $M_1$, and the data `Module.Presentation.CokernelData`: for each generator $x$ of $M_1$, a linear combination of the generators of $M_2$ equal to $f(x)$. The generators of the cokernel are those of $M_2$, and the relations are those of $M_2$ together with these combinations. For the tensor product, the generators are the pairs of generators, and the relations are the relations of $M_1$ tensored with the generators of $M_2$, and conversely. For the differentials, a presentation of $S$ as an $R$-algebra by polynomials gives a presentation of $\Omega_{S/R}$ over $S$: one generator $dx_i$ for each variable, and one relation $df$ for each relation $f$ of the algebra.

**Theorem.** A module is free if and only if it has a presentation with no relations.

*Proof.* A presentation with no relations has $\pi : A^{(G)} \to M$ surjective with kernel $0$, so $M \simeq A^{(G)}$. Conversely, a basis indexed by $G$ gives the presentation of $A^{(G)}$ with no relations, moved along the equivalence to $M$. $\square$

This is `Module.free_iff_exists_presentation`, and `Module.Relations.Solution.IsPresentation.free` is one direction.

#### Finitely presented modules

The class `Module.FinitePresentation R M` says that there is a finite set $s \subseteq M$ that spans $M$ such that the kernel of $R^{(s)} \to M$ is finitely generated (`Module.FinitePresentation.out`). It is defined over a semiring, but most results use a ring.

**Theorem.** A module is finitely presented if and only if it has a presentation with finitely many generators and finitely many relations.

*Proof.* If $s$ spans $M$ and the kernel $K$ of $R^{(s)} \to M$ is spanned by a finite set $t$, then $s$ and $t$ give a presentation with finite $G$ and $R$, by the criterion above. Conversely, a presentation with finite $G$ and $R$ gives the spanning family $(v_g)$, and the kernel of $R^{(G)} \to M$ is the span of the finitely many relations. A change from $G$ to the finite set of the $v_g$ keeps the kernel finitely generated. $\square$

This is `Module.finitePresentation_iff_exists_presentation`, with `Module.Presentation.finitePresentation` for one direction. A finitely presented module is finite, by the instance `instFiniteOfFinitePresentation`. Finite free modules such as $R^n$ are finitely presented (`instFinitePresentationForall`), and so are finite projective modules (`Module.finitePresentation_of_projective`). The class is kept by finite products (`Module.FinitePresentation.prod`, `Module.FinitePresentation.pi`), by base change (`instFinitePresentationTensorProduct`), and by linear equivalences (`Module.FinitePresentation.of_equiv`). If $S$ is finitely presented as an $R$-module and $M$ is finitely presented over $S$, then $M$ is finitely presented over $R$ (`Module.FinitePresentation.trans`).

The definition does not depend on the choice of the generators.

**Theorem.** Let $l : M \to N$ be surjective, with $M$ finite and $N$ finitely presented. Then $\ker l$ is finitely generated.

*Proof.* Take a surjection $\varphi : R^n \to N$ with finitely generated kernel $K$. Since $l$ is surjective, $\varphi = l \circ \psi$ for some $\psi : R^n \to M$. For $m \in M$ write $l(m) = \varphi(a)$; then $m - \psi(a) \in \ker l$, so $M = \psi(R^n) + \ker l$. Thus the map $\ker l \to M / \psi(R^n)$ is surjective, and its target is finitely generated since $M$ is finite. Its kernel is $\ker l \cap \psi(R^n)$, and $\psi(a) \in \ker l$ means $\varphi(a) = 0$, so this kernel is $\psi(K)$, which is finitely generated. An extension of a finitely generated module by a finitely generated module is finitely generated. $\square$

This is `Module.FinitePresentation.fg_ker`, and `Module.FinitePresentation.fg_ker_iff` is the converse for a finitely generated kernel. In an exact sequence $0 \to K \to M \to N \to 0$: if $M$ is finitely presented and $K$ is finitely generated, then $N$ is finitely presented (`Module.finitePresentation_of_surjective`); if $K$ and $N$ are finitely presented, then $M$ is (`Module.finitePresentation_of_ker`).

**Theorem.** Over a Noetherian ring, a module is finitely presented if and only if it is finitely generated.

*Proof.* Let $M$ be finitely generated, with a surjection $R^n \to M$. Over a Noetherian ring, $R^n$ is a Noetherian module, so its submodule $\ker(R^n \to M)$ is finitely generated. $\square$

This is `Module.finitePresentation_iff_finite`. Over the ring $k[x_1, x_2, \ldots]$ of polynomials in infinitely many variables, the module $k$ is finitely generated and not finitely presented.

Finite presentation is the condition under which $\operatorname{Hom}$ commutes with localization. For $M$ finitely presented and a multiplicative set $S$, the localized map $\operatorname{Hom}(M, N) \to \operatorname{Hom}(S^{-1}M, S^{-1}N)$ is a localization (`Module.FinitePresentation.isLocalizedModule_map`), and `Module.FinitePresentation.linearEquivMap` is the equivalence $S^{-1}\operatorname{Hom}(M, N) \simeq \operatorname{Hom}(S^{-1}M, S^{-1}N)$. A map that is bijective after localization at a prime $\mathfrak{p}$ is already bijective after localization at one element $g \notin \mathfrak{p}$ (`Module.FinitePresentation.exists_notMem_bijective`).

#### Common errors

1. Using `Module.Relations` over a semiring. The presentation API needs a ring, since the quotient by the relations is a quotient by a submodule. The class `Module.FinitePresentation` is defined over a semiring, but its main results also need a ring.
2. Expecting each finitely generated module to be finitely presented. This needs a Noetherian ring and `Module.finitePresentation_iff_finite`.
3. Building the presentation of a cokernel without the lifts. `Module.Presentation.cokernel` needs `Module.Presentation.CokernelData`, which gives the image of each generator of $M_1$ as a combination of the generators of $M_2$; for a free $M_2$, `Module.Presentation.CokernelData.ofSection` builds it from a section of $\pi$.

### Exercises

1. (A) Give a presentation of $\mathbb{Z}/6$ over $\mathbb{Z}$ with one generator and one relation, and check the criterion `Module.Relations.Solution.isPresentation_iff`.
2. (A) Give a presentation of $\mathbb{Z}/2 \oplus \mathbb{Z}/3$ with two generators, and show that the module is also presented by one generator.
3. (B) Show that the module with generators $e_1, e_2$ and the relation $2 e_1 - 4 e_2 = 0$ over $\mathbb{Z}$ is $\mathbb{Z} \oplus \mathbb{Z}/2$.
4. (B) Show that a direct summand of a finitely presented module is finitely presented.
5. (B) Let $R = k[x_1, x_2, \ldots]$. Show that the ideal $(x_1, x_2, \ldots)$ is not finitely generated, and conclude that $R / (x_1, x_2, \ldots)$ is not finitely presented.
6. (C) Use the presentation of the tensor product to show that $\mathbb{Z}/m \otimes \mathbb{Z}/n \simeq \mathbb{Z}/\gcd(m, n)$.

### Reference

<?reference?>
