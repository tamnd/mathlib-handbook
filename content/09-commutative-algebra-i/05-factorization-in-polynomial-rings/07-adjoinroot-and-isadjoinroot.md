---
title: AdjoinRoot and IsAdjoinRoot
kind: api
modules:
  - Mathlib.RingTheory.AdjoinRoot
  - Mathlib.RingTheory.IsAdjoinRoot
  - Mathlib.RingTheory.Adjoin.PowerBasis
  - Mathlib.RingTheory.Localization.Away.AdjoinRoot
  - Mathlib.RingTheory.Ideal.MonicSpan
explains:
  E2: [AdjoinRoot.mk_eq_mk, AdjoinRoot.isField_iff_irreducible, "AdjoinRoot.powerBasis'", AdjoinRoot.equiv, IsAdjoinRoot.map_eq_zero_iff, IsAdjoinRoot.algEquiv, IsAdjoinRootMonic.basis, Localization.awayEquivAdjoin, Polynomial.exists_monic_span]
  E1: auto
families: []
requires: [V06.C05, V06.C06, V07.C02, V09.C01, V09.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## AdjoinRoot and IsAdjoinRoot

### Overview

The section on derivatives and multiple roots builds the ring $R[X]/(f)$ and its root, the class of $X$. This section is the library around that construction. It has two layers. The type `AdjoinRoot f` is one fixed model of $R[X]/(f)$, with a large API of maps, equivalences, bases and ring properties. The structure `IsAdjoinRoot S f` is a presentation: it says that a given $R$-algebra $S$ is $R[X]/(f)$ through a chosen surjection $R[X] \to S$ with kernel $(f)$. Most theorems about a ring of the form $R[\alpha]$ use the second layer, because the ring $S$ in a real application is never the type `AdjoinRoot f` itself.

Three smaller modules complete the picture. `Mathlib.RingTheory.Adjoin.PowerBasis` gives a power basis of $K[x]$ for an integral element $x$ over a field $K$. `Mathlib.RingTheory.Localization.Away.AdjoinRoot` identifies the localization $R[1/r]$ with $R[X]/(rX - 1)$. `Mathlib.RingTheory.Ideal.MonicSpan` states that each nonzero ideal of $k[X]$ has a monic generator. Linear algebra over $R$ (bases, `Module.finrank`) comes from Volume 7, and the quotient rings come from Volume 6.

### The library around it

#### The model AdjoinRoot

For $f \in R[X]$ over a commutative ring $R$, `AdjoinRoot f` is the quotient `R[X] ⧸ Ideal.span {f}`. The maps `AdjoinRoot.mk f : R[X] →+* AdjoinRoot f` and `AdjoinRoot.of f : R →+* AdjoinRoot f` and the element `AdjoinRoot.root f` have their treatment in the earlier section. The basic equality test is `AdjoinRoot.mk_eq_mk`:
$$\operatorname{mk}(g) = \operatorname{mk}(h) \iff f \mid g - h.$$
The proof is one line: $\operatorname{mk}(g) - \operatorname{mk}(h) = \operatorname{mk}(g - h)$, and `AdjoinRoot.mk_eq_zero` says that this is zero exactly when $f \mid g - h$.

The ring properties of `AdjoinRoot f` follow from the properties of the ideal $(f)$. Over a field $K$, `AdjoinRoot.isField_iff_irreducible` gives $\operatorname{IsField}(K[X]/(f)) \iff f$ irreducible. Proof sketch: $K[X]$ is a principal ideal domain, so a nonzero ideal $(f)$ is maximal exactly when $f$ is irreducible, and a quotient by an ideal is a field exactly when the ideal is maximal. When $f$ is prime, `AdjoinRoot.isDomain_of_prime` gives a domain. The instance `AdjoinRoot.instIsNoetherianRing` makes $R[X]/(f)$ Noetherian when $R$ is Noetherian, and `AdjoinRoot.finitePresentation` makes it a finitely presented $R$-algebra.

The maps between these rings form a small family. The table lists the main ones.

| Lean name | Statement |
| --- | --- |
| `AdjoinRoot.algHomOfDvd` | for $g \mid f$, the map $R[X]/(f) \to R[X]/(g)$ |
| `AdjoinRoot.algEquivOfEq` | equal polynomials give equal quotients |
| `AdjoinRoot.algEquivOfAssociated` | associated polynomials give isomorphic quotients |
| `AdjoinRoot.mapAlgHom` | a map $R[X]/(p) \to S[X]/(q)$ when $q$ divides the image of $p$ |
| `AdjoinRoot.quotEquivQuotMap` | $(R[X]/(f))/I \cong (R/I)[X]/(\bar f)$ |
| `AdjoinRoot.tensorAlgEquiv` | base change of $R[X]/(f)$ along $R \to T$ is $T[X]/(f)$ |
| `AdjoinRoot.Minpoly.toAdjoin` | the surjection $R[X]/(\operatorname{minpoly} x) \to R[x]$ |

The isomorphism `AdjoinRoot.quotEquivQuotMap` is the algebra form of the statement "reduce the coefficients modulo $I$". In number theory $I$ is often $p\mathbb{Z}$ for a prime $p$, and $\bar f$ is $f$ modulo $p$.

The universal property gives a count of algebra maps. For a field $F$, a domain $L$ over $F$ and $f \ne 0$, `AdjoinRoot.equiv` is a bijection between the $F$-algebra maps $F[X]/(f) \to L$ and the roots of $f$ in $L$ (the type `f.aroots L`). Proof sketch: `AdjoinRoot.liftAlgHom` sends a root $x$ to the map with $\operatorname{root} f \mapsto x$, and a map $\varphi$ goes to $\varphi(\operatorname{root} f)$, which is a root because $f(\operatorname{root} f) = 0$. The two maps are inverse because an algebra map out of $F[X]/(f)$ is determined by the image of the root.

#### Monic polynomials and power bases

When $g$ is monic, division with remainder by $g$ works over each commutative ring. The linear map `AdjoinRoot.modByMonicHom` sends a class to its reduced representative, and `AdjoinRoot.modByMonicHom_mk` says that it sends $\operatorname{mk}(f)$ to `f %ₘ g`. This gives `AdjoinRoot.powerBasis'`, a power basis of $R[X]/(g)$ over $R$ with generator the root and dimension `g.natDegree` (the lemma `AdjoinRoot.powerBasis'_dim`). So $R[X]/(g)$ is a free $R$-module with basis $1, \alpha, \dots, \alpha^{n-1}$, where $n = \deg g$. Proof sketch: each class has a unique representative of degree less than $n$, and such a representative is a unique $R$-combination of $1, X, \dots, X^{n-1}$.

The same monic hypothesis gives `Polynomial.Monic.free_adjoinRoot`, `Polynomial.Monic.finite_adjoinRoot` and `AdjoinRoot.isIntegral_of_monic`. When also $\deg g > 0$, `AdjoinRoot.of.injective_of_monic_of_degree_pos` says that $R \to R[X]/(g)$ is injective. Without the monic hypothesis this is false: over $\mathbb{Z}/4$ the polynomial $2X + 1$ is a unit, and its quotient is the zero ring. The theorem `Polynomial.Monic.exists_splits_map` iterates the construction: a monic $p$ over a nontrivial ring splits in some finite, free, nontrivial $R$-algebra.

Over a field the root has a known minimal polynomial. `AdjoinRoot.minpoly_root` says that for $f \ne 0$ the minimal polynomial of the root is $f$ divided by its leading coefficient. `AdjoinRoot.minpoly_powerBasis_gen_of_monic` is the monic case.

#### Presentations: IsAdjoinRoot

A term `h : IsAdjoinRoot S f` has three fields: `h.map : R[X] →ₐ[R] S`, the proof `h.map_surjective`, and `h.ker_map : RingHom.ker h.map = Ideal.span {f}`. It is a structure, not a `Prop`, because the map is data. The root is `h.root`, the image of $X$, and `h.repr` picks a preimage in $R[X]$ of an element of $S$. The basic lemmas copy those of `AdjoinRoot`: `IsAdjoinRoot.map_eq_zero_iff` says $h.\operatorname{map}(p) = 0 \iff f \mid p$, and `IsAdjoinRoot.aeval_root_self` says $f(h.\operatorname{root}) = 0$. The first is the statement of `h.ker_map` read element by element.

The universal property is `IsAdjoinRoot.lift` (a ring map out of $S$ from a root $x$ of $f$ in $T$) with `IsAdjoinRoot.lift_root`, and `IsAdjoinRoot.liftHom` for algebra maps. Two presentations of the same polynomial give isomorphic rings: `IsAdjoinRoot.algEquiv` is an $R$-algebra isomorphism $S \cong T$, and `IsAdjoinRoot.algEquiv_root` says that it sends root to root. Proof sketch: lift each root to the other ring. The two compositions fix the root, and a map out of $S$ is determined by the image of the root (`IsAdjoinRoot.ext`). The special case `IsAdjoinRoot.adjoinRootAlgEquiv` is the isomorphism `AdjoinRoot f ≃ₐ[R] S`. In the other direction, `AdjoinRoot.isAdjoinRoot` presents the model itself, and `IsAdjoinRoot.ofAlgEquiv` moves a presentation along an isomorphism.

The structure `IsAdjoinRootMonic S f` extends `IsAdjoinRoot S f` with the field `monic`. It gives the basis `IsAdjoinRootMonic.basis : Basis (Fin f.natDegree) R S`, with `IsAdjoinRootMonic.basis_apply` saying that the $i$-th vector is $h.\operatorname{root}^i$. The coordinates are `IsAdjoinRootMonic.coeff`, and `IsAdjoinRootMonic.coeff_root_pow` says that $\alpha^n$ has the coordinate vector `Pi.single n 1` for $n < \deg f$. Then `IsAdjoinRootMonic.powerBasis` and `IsAdjoinRootMonic.finrank` give $\operatorname{finrank}_R S = \deg f$ over a ring with the strong rank condition.

Presentations also come from primitive elements. Let $R$ be an integrally closed domain and $S$ a domain that is torsion free over $R$. When $\alpha \in S$ is integral and $R[\alpha] = S$, `IsAdjoinRoot.mkOfAdjoinEqTop` gives `IsAdjoinRoot S (minpoly R α)`. Under the same hypotheses, `IsAdjoinRootMonic.minpoly_eq` says that the minimal polynomial of the root of an irreducible monic $f$ is $f$. These results use the theory of integral closure, and the text states them without proof.

#### Power bases of K[x]

Let $K$ be a field and $x$ an element of a $K$-algebra $S$ that is integral over $K$. `Algebra.adjoin.powerBasis` is a power basis of the subalgebra $K[x]$, with generator $x$ (`Algebra.adjoin.powerBasis_gen`) and dimension the degree of the minimal polynomial (`Algebra.adjoin.powerBasis_dim`). When $K[x] = S$, `PowerBasis.ofAdjoinEqTop` gives a power basis of $S$ itself. The theorems `PowerBasis.repr_mul_isIntegral` and `PowerBasis.repr_pow_isIntegral` are for towers $R \to S \to A$: if the coordinates of $x$ and $y$ in a power basis are integral over $R$, and the minimal polynomial of the generator comes from $R$, then the coordinates of $xy$ are integral over $R$.

#### Localization as a quotient

The localization $R[1/r]$ is the ring with one new element $t$ and one relation $rt = 1$. `Localization.awayEquivAdjoin` is the $R$-algebra isomorphism
$$R[1/r] \cong R[X]/(rX - 1),$$
written `Localization.Away r ≃ₐ[R] AdjoinRoot (C r * X - 1)`. The core fact is `IsLocalization.adjoin_inv`, which says that `AdjoinRoot (C r * X - 1)` satisfies the predicate `IsLocalization.Away r`. Proof sketch: `AdjoinRoot.root_isInv` says $r \cdot \operatorname{root} = 1$, so $r$ becomes a unit. A ring map $\varphi : R \to T$ with $\varphi(r)$ a unit sends $X$ to $\varphi(r)^{-1}$, and this map kills $rX - 1$. Uniqueness of localization then gives the isomorphism. As a consequence, `IsLocalization.Away.finitePresentation` says that $R[1/r]$ is a finitely presented $R$-algebra, with one generator and one relation.

#### Monic generators of ideals

`Polynomial.exists_monic_span` says that over a field $k$ each nonzero ideal $I$ of $k[X]$ is `Ideal.span {f}` for a monic $f$. Proof: $k[X]$ is a principal ideal domain, so $I = (g)$ with $g \ne 0$, and $f = g / \operatorname{lc}(g)$ is monic and associated to $g$. The relative version `Polynomial.exists_monic_span_sup_map_eq` is for an ideal $p$ of $R[X]$ over a general $R$: if $\mathfrak m = p \cap R$ is maximal and $p \ne \mathfrak m R[X]$, then $p = \mathfrak m R[X] + (f)$ for a monic $f$. The text states it without proof.

#### Common errors

1. Forgetting the monic hypothesis. `AdjoinRoot.powerBasis'` and `IsAdjoinRootMonic.basis` need a monic polynomial. Over a field, use `AdjoinRoot.powerBasis` with the hypothesis $f \ne 0$. Over a general ring with $f$ not monic, $R[X]/(f)$ can be zero or not free.
2. Proving facts about `AdjoinRoot f` when the ring in the goal is another type $S$. First build `h : IsAdjoinRoot S f`, then use the `IsAdjoinRoot` and `IsAdjoinRootMonic` lemmas, or transport with `IsAdjoinRoot.adjoinRootAlgEquiv`.
3. Expecting `simp` to reduce `AdjoinRoot.mk f g` to a normal form. The quotient has no computed normal form in general. Use `AdjoinRoot.mk_eq_mk` to reduce an equality to divisibility, or use `AdjoinRoot.modByMonicHom` when $f$ is monic.

### Exercises

1. (A) Use `AdjoinRoot.mk_eq_mk` to show that in $\mathbb{Q}[X]/(X^2 - 2)$ the classes of $X^3$ and $2X$ are equal.
2. (A) Show that $\mathbb{R}[X]/(X^2 + 1)$ is a field and that $\mathbb{R}[X]/(X^2 - 1)$ is not, with `AdjoinRoot.isField_iff_irreducible`.
3. (A) Use `AdjoinRoot.equiv` to count the $\mathbb{Q}$-algebra maps $\mathbb{Q}[X]/(X^3 - 2) \to \mathbb{R}$ and $\mathbb{Q}[X]/(X^3 - 2) \to \mathbb{C}$.
4. (B) Let $h : \operatorname{IsAdjoinRootMonic}\ S\ f$ with $\deg f = n$. Show that each $s \in S$ is $\sum_{i < n} c_i \alpha^i$ for unique $c_i \in R$, with `IsAdjoinRootMonic.basis`.
5. (B) Show directly that $\mathbb{Z}[1/2] \cong \mathbb{Z}[X]/(2X - 1)$, and compare with `Localization.awayEquivAdjoin`.
6. (C) Let $I$ be an ideal of $R$ and $f \in R[X]$ monic. Use `AdjoinRoot.quotEquivQuotMap` to show that $(R[X]/(f))/I(R[X]/(f))$ is free over $R/I$ of rank $\deg f$.

### Reference

<?reference?>
