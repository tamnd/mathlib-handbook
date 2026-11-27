---
title: Reflections and root pairings
kind: theory
modules:
  - Mathlib.LinearAlgebra.Reflection
  - Mathlib.LinearAlgebra.RootSystem.Defs
  - Mathlib.LinearAlgebra.RootSystem.Basic
  - Mathlib.LinearAlgebra.RootSystem.Hom
  - Mathlib.LinearAlgebra.RootSystem.WeylGroup
  - Mathlib.LinearAlgebra.RootSystem.Reduced
  - Mathlib.LinearAlgebra.RootSystem.Irreducible
  - Mathlib.LinearAlgebra.RootSystem.OfBilinear
  - Mathlib.LinearAlgebra.RootSystem.IsValuedIn
  - Mathlib.LinearAlgebra.RootSystem.RootPairingCat
  - Mathlib.LinearAlgebra.RootSystem.BaseChange
explains:
  E3: [Module.reflection, Module.infinite_range_reflection_reflection_iterate_iff, RootPairing, RootPairing.IsRootSystem, RootPairing.reflection, RootPairing.ext, RootPairing.mk'', RootPairing.Hom, RootPairing.weylGroup, RootPairing.IsReduced, RootPairing.coxeterWeight_eq_four_iff_not_linearIndependent, RootPairing.IsIrreducible, RootPairing.ofBilinear, RootPairing.IsValuedIn, RootPairing.IsCrystallographic]
  E2: [Module.preReflection, Module.reflection_apply, Module.reflection_mul_reflection_pow_apply, Module.injOn_dualMap_subtype_span_range_range, RootPairing.pairing, RootPairing.coroot', RootPairing.coreflection, RootPairing.reflection_dualMap_eq_coreflection, RootPairing.coxeterWeight, RootPairing.flip, RootDatum, RootPairing.reflectionPerm, RootPairing.reflectionPerm_root, RootPairing.Equiv, RootPairing.Aut, RootPairing.Equiv.reflection, RootPairing.weylGroupToPerm, RootPairing.isSimpleModule_weylGroupRootRep_iff, RootPairing.infinite_of_linearIndependent_coxeterWeight_four, RootPairing.pairing_two_two_iff, RootPairing.isRootSystem_mk'', LinearMap.IsReflective, RootPairing.pairingIn, RootPairingCat, RootPairing.restrictScalarsRat, RootPairing.IsBalanced]
  E1: auto
families: []
requires: [V05.C06, V07.C06, V08.C05, V29.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Reflections and root pairings

### Overview

Chapter 6 attached to a semisimple Lie algebra a finite set of vectors in $H^*$, the roots, and a coroot $h_\alpha \in H$ for each of them, with $\alpha(h_\alpha) = 2$ and with the reflections $\beta \mapsto \beta - \beta(h_\alpha)\alpha$ permuting the roots. This chapter studies such configurations without the Lie algebra. Mathlib does not use a Euclidean space. It takes two modules $M$ and $N$ over a commutative ring $R$ in perfect duality, roots in $M$ and coroots in $N$. Since the coroots are data, the definition works over $\mathbb{Z}$, where it gives root data, and for infinite families.

The section proves that over a field of characteristic $0$ the roots of a finite root system determine the coroots, that two independent roots of a finite pairing have Coxeter weight different from $4$, and that symmetric bilinear forms give root pairings. The examples are $A_1$, $A_2$, $B_2$ and $G_2$ with coordinates.

### Definitions

Fix a commutative ring $R$ and $R$-modules $M$, $N$.

**Definition (Reflection).** Let $x \in M$ and $f \in M^* = \operatorname{Hom}_R(M, R)$. The *pre-reflection* is the linear map $s_{x,f}(y) = y - f(y)\,x$. If $f(x) = 2$, it is a *reflection*: it sends $x$ to $-x$, fixes $\ker f$ pointwise, and $s_{x,f}^2 = 1$ because $f(s_{x,f}(y)) = -f(y)$.

**Definition (Root pairing).** A *root pairing* $P$ indexed by a type $\iota$ consists of a perfect pairing $\langle \cdot , \cdot \rangle : M \times N \to R$, injective families $\alpha : \iota \to M$ (the roots) and $\alpha^\vee : \iota \to N$ (the coroots), and permutations $\sigma_i$ of $\iota$, such that for all $i, j$:

1. $\langle \alpha_i, \alpha_i^\vee \rangle = 2$;
2. $\alpha_j - \langle \alpha_j, \alpha_i^\vee \rangle\,\alpha_i = \alpha_{\sigma_i(j)}$;
3. $\alpha_j^\vee - \langle \alpha_i, \alpha_j^\vee \rangle\,\alpha_i^\vee = \alpha_{\sigma_i(j)}^\vee$.

The *pairing* is $p_{ij} = \langle \alpha_i, \alpha_j^\vee \rangle$, so $p_{ii} = 2$. The reflection $s_i$ of $M$ is $s_{x,f}$ for $x = \alpha_i$ and $f = \langle \cdot, \alpha_i^\vee \rangle$, and condition 2 says $s_i(\alpha_j) = \alpha_{\sigma_i(j)}$. Condition 3 says the same for the coreflection $s_i^\vee$ of $N$.

**Definition (Root system and root datum).** A root pairing is a *root system* if the roots span $M$ and the coroots span $N$. A *root datum* is a root pairing over $R = \mathbb{Z}$. A root pairing is *finite* if $\iota$ is finite.

**Definition (Coxeter weight).** The *Coxeter weight* of $i, j$ is $c_{ij} = p_{ij}\,p_{ji}$.

**Definition (Morphism).** A morphism from $P$ to $Q$ (on $M_2$, $N_2$, $\iota_2$) is a linear map $w : M \to M_2$, a linear map $w^\vee : N_2 \to N$ and a bijection $e : \iota \to \iota_2$, such that $\langle w(m), n \rangle_Q = \langle m, w^\vee(n) \rangle_P$, $w(\alpha_i) = \alpha_{e(i)}$ and $w^\vee(\alpha^\vee_{e(i)}) = \alpha^\vee_i$. An *equivalence* is a morphism with $w$ and $w^\vee$ bijective, and the equivalences from $P$ to $P$ form the automorphism group $\operatorname{Aut}(P)$.

**Definition (Weyl group).** Each $s_i$, with the coreflection $s_i^\vee$ and the permutation $\sigma_i$, is an automorphism of $P$. The *Weyl group* $W(P)$ is the subgroup of $\operatorname{Aut}(P)$ generated by these reflections.

**Definition (Reduced, irreducible).** $P$ is *reduced* if, whenever $\alpha_i$ and $\alpha_j$ are linearly dependent, $\alpha_i = \alpha_j$ or $\alpha_i = -\alpha_j$. $P$ is *irreducible* if $M$ and $N$ are nonzero, every submodule $q \neq 0$ of $M$ stable under all $s_i$ is $M$, and every submodule $q \neq 0$ of $N$ stable under all $s_i^\vee$ is $N$.

**Definition (Valued in a subring).** Let $S \to R$ be a ring map. $P$ is *valued in* $S$ if every $p_{ij}$ is the image of an element of $S$. It is *crystallographic* if it is valued in $\mathbb{Z}$.

**Definition (Reflective vector).** Let $B$ be a bilinear form on $M$. A vector $x$ is *reflective* for $B$ if $B(x, x)$ is a regular element of $R$ (multiplication by it is injective) and $B(x, x)$ divides $2B(x, y)$ for every $y$. Then $c_x(y)$, the unique element with $B(x, x)\,c_x(y) = 2B(x, y)$, is a linear form with $c_x(x) = 2$.

### Theorems and proofs

**Proposition (Reflections preserve the pairing).** In a root pairing, $\langle s_i(m), s_i^\vee(n) \rangle = \langle m, n \rangle$ for all $m \in M$, $n \in N$. Since $(s_i^\vee)^2 = 1$, $s_i^\vee$ is the transpose of $s_i$.

*Proof.* Write $a = \langle m, \alpha_i^\vee \rangle$ and $b = \langle \alpha_i, n \rangle$. Then $s_i(m) = m - a\alpha_i$ and $s_i^\vee(n) = n - b\alpha_i^\vee$. Expand: $\langle m - a\alpha_i, n - b\alpha_i^\vee \rangle = \langle m, n \rangle - b a - a b + a b \langle \alpha_i, \alpha_i^\vee \rangle = \langle m, n \rangle - 2ab + 2ab = \langle m, n \rangle$. $\square$

For the next theorem take $x, y \in M$ and $f, g \in M^*$ with $f(x) = g(y) = 2$, and let $u = s_{x,f} \circ s_{y,g}$.

**Theorem (Coxeter weight four gives an infinite orbit).** Suppose $f(y)\,g(x) = 4$ and $M$ is torsion free over $\mathbb{Z}$. Put $a = f(y)$ and $v = a x - 2y$. Then $u^n(y) = y + n v$ for all $n \geq 0$. So the orbit of $y$ is infinite if and only if $a x \neq 2y$.

*Proof.* Put $b = g(x)$, so $ab = 4$. Step 1: $u(y) = s_{x,f}(-y) = -y + a x = y + v$. Step 2: $u(x) = s_{x,f}(x - b y) = -x - b(y - a x) = (ab - 1)x - by = 3x - by$. Step 3: $u(v) = a(3x - by) - 2(-y + ax) = a x - (ab - 2) y = a x - 2y = v$. Step 4: by induction, $u^{n+1}(y) = u(y + nv) = y + v + nv$. Step 5: if $v \neq 0$, the vectors $y + nv$ are pairwise distinct, because $(n - m)v = 0$ with $n \neq m$ forces $v = 0$ in a torsion free group. If $v = 0$, the orbit is $\{y\}$. $\square$

**Theorem (Reflections with a common root).** Let $R$ be a field of characteristic $0$ and $\Phi \subseteq M$ a finite set that spans $M$. Let $x \in \Phi$ and $f, g \in M^*$ with $f(x) = g(x) = 2$, and suppose $s_{x,f}$ and $s_{x,g}$ both map $\Phi$ into $\Phi$. Then $f = g$.

*Proof.* Step 1: an injective map of the finite set $\Phi$ into itself is onto, so $u = s_{x,f} \circ s_{x,g}$ permutes $\Phi$, and $u^k$ fixes $\Phi$ pointwise for some $k \geq 1$. Step 2: compute $u(y) = s_{x,f}(y - g(y)x) = y - f(y)x - g(y)(-x) = y + h(y)\,x$ with $h = g - f$. Step 3: $h(x) = 2 - 2 = 0$, so $u(x) = x$ and by induction $u^k(y) = y + k\,h(y)\,x$. Step 4: for $y \in \Phi$, $u^k(y) = y$ gives $k\,h(y)\,x = 0$. Since $x \neq 0$ (as $f(x) = 2$) and $k \neq 0$ in $R$, $h(y) = 0$. Step 5: $h$ vanishes on a spanning set, so $h = 0$. $\square$

**Corollary (The roots determine the coroots).** Over a field of characteristic $0$, let $P$ be a finite root system. Then $\alpha_i^\vee$ is the unique $n \in N$ with $\langle \alpha_i, n \rangle = 2$ such that $m \mapsto m - \langle m, n \rangle \alpha_i$ preserves the set of roots. In particular, given roots that span and for each $i$ some coroot whose reflection preserves the roots, the permutations $\sigma_i$ and condition 3 come for free.

*Proof.* Apply the theorem with $\Phi$ the set of roots and $f$, $g$ the forms $\langle \cdot, n \rangle$ and $\langle \cdot, \alpha_i^\vee \rangle$; the pairing is perfect, so $f = g$ gives $n = \alpha_i^\vee$. For the second claim, $\sigma_i$ is read from $s_i(\alpha_j) = \alpha_{\sigma_i(j)}$. By the previous proposition $\langle \alpha_{\sigma_i(j)}, s_i^\vee(\alpha_j^\vee) \rangle = \langle \alpha_j, \alpha_j^\vee \rangle = 2$, and its reflection is $s_i s_j s_i$, which preserves the roots. By uniqueness it equals $\alpha^\vee_{\sigma_i(j)}$. $\square$

**Theorem (Coxeter weight four).** Let $P$ be a finite root pairing, $R$ a domain of characteristic $0$ and $M$ torsion free. Then $\alpha_i$ and $\alpha_j$ are linearly independent if and only if $c_{ij} \neq 4$.

*Proof.* Step 1: suppose $r\alpha_i = r'\alpha_j$ with $(r, r') \neq (0, 0)$. If $r = 0$, then $r'\alpha_j = 0$ with $r' \neq 0$, so $\alpha_j = 0$ by torsion freeness, which contradicts $\langle \alpha_j, \alpha_j^\vee \rangle = 2 \neq 0$. So $r \neq 0$ and in the same way $r' \neq 0$. Pair the relation with $\alpha_i^\vee$ and with $\alpha_j^\vee$: $2r = r' p_{ji}$ and $r p_{ij} = 2r'$. Multiply: $4rr' = c_{ij}\,rr'$, and since $rr' \neq 0$ in a domain, $c_{ij} = 4$. Step 2: suppose $\alpha_i$ and $\alpha_j$ are independent and $c_{ij} = 4$. Apply the infinite orbit theorem to $s_i$ and $s_j$: $f(y) g(x) = p_{ji} p_{ij} = 4$, and $v = p_{ji}\alpha_i - 2\alpha_j \neq 0$ by independence. The orbit $\{\alpha_j + n v\}$ consists of roots, since $u = s_i s_j$ permutes the roots, and it is infinite. This contradicts the finiteness of $\iota$. $\square$

**Proposition (The Weyl group acts faithfully on the roots).** If the roots span $M$, the map $W(P) \to \operatorname{Perm}(\iota)$, $w \mapsto e_w$ with $w(\alpha_i) = \alpha_{e_w(i)}$, is an injective homomorphism. So a finite root system has a finite Weyl group.

*Proof.* Step 1: the map is a homomorphism because $w w'(\alpha_i) = w(\alpha_{e_{w'}(i)}) = \alpha_{e_w e_{w'}(i)}$, and the roots are injective. Step 2: if $e_w$ is the identity, then $w(\alpha_i) = \alpha_i$ for all $i$, so $w = 1$ on $M$ because the roots span. Step 3: perfectness and $\langle w(m), n \rangle = \langle m, w^\vee(n) \rangle$ make $w^\vee = 1$ too. $\square$

**Theorem (Root pairings from bilinear forms).** Let $B$ be a symmetric nondegenerate bilinear form on $M$ and $x$ reflective for $B$. Then the reflection $s_x(y) = y - c_x(y)\,x$ preserves $B$ and maps reflective vectors to reflective vectors. So the reflective vectors are the roots of a root pairing between $M$ and $M^*$, with coroots $c_x$.

*Proof.* Step 1: $B(x, x)\,c_x(y) = 2B(x, y)$ for all $y$. Step 2: expand $B(s_x y, s_x z) = B(y, z) - c_x(z) B(y, x) - c_x(y) B(x, z) + c_x(y) c_x(z) B(x, x)$. By Step 1 the last term is $2c_x(y) B(x, z)$. Multiply the sum of the three correction terms by $B(x, x)$: $-2B(x,z)B(y,x) - 2B(x,y)B(x,z) + 4B(x,y)B(x,z) = 0$ by symmetry. Since $B(x, x)$ is regular, the sum is $0$, so $B(s_x y, s_x z) = B(y, z)$. Step 3: if $g$ preserves $B$ and is invertible, and $z$ is reflective, then $B(gz, gz) = B(z, z)$ is regular and $B(gz, y) = B(z, g^{-1}y)$, so $B(gz, gz)$ divides $2B(gz, y)$. Thus $g z$ is reflective. Step 4: $c_{s_x z}(y) = c_z(s_x y)$ by Steps 1 and 2, so the transpose of $s_x$ permutes the coroots in the matching way. $\square$

### Examples

In each example $M = N \subseteq \mathbb{Q}^n$ with the dot product and $\alpha^\vee = 2\alpha / (\alpha \cdot \alpha)$. Then $p_{ij} = 2(\alpha_i \cdot \alpha_j)/(\alpha_j \cdot \alpha_j)$ and $c_{ij} = 4\cos^2\theta$, where $\theta$ is the angle between the roots.

**Example (A1).** $M = \mathbb{Q}$, roots $\pm 1$, coroots $\pm 2$, pairing the product. Then $\langle 1, 2 \rangle = 2$, the reflection is $y \mapsto -y$, and $W = \{\pm 1\}$.

**Example (A2).** $M = \{x \in \mathbb{Q}^3 : x_1 + x_2 + x_3 = 0\}$, with the six roots $\varepsilon_i - \varepsilon_j$, $i \neq j$, all of square length $2$, so $\alpha^\vee = \alpha$. For $\alpha_1 = \varepsilon_1 - \varepsilon_2$ and $\alpha_2 = \varepsilon_2 - \varepsilon_3$, $\alpha_1 \cdot \alpha_2 = -1$, so $p_{12} = p_{21} = -1$ and $c_{12} = 1$, an angle of $120$ degrees. The reflection $s_1$ swaps the first two coordinates, so $W(A_2) \cong S_3$, of order $6$. In the plane the six roots are the vertices of a regular hexagon.

**Example (B2).** $M = \mathbb{Q}^2$, with the four short roots $\pm \varepsilon_1$, $\pm \varepsilon_2$ and the four long roots $\pm \varepsilon_1 \pm \varepsilon_2$. Take $\alpha_1 = \varepsilon_1 - \varepsilon_2$ (long, $\alpha_1^\vee = \alpha_1$) and $\alpha_2 = \varepsilon_2$ (short, $\alpha_2^\vee = 2\varepsilon_2$). Then $p_{12} = \langle \alpha_1, \alpha_2^\vee \rangle = -2$ and $p_{21} = \langle \alpha_2, \alpha_1^\vee \rangle = -1$, so $c_{12} = 2$, an angle of $135$ degrees. The Weyl group is the group of signed permutations of two coordinates, the dihedral group of order $8$.

**Example (G2).** $M = \{x \in \mathbb{Q}^3 : x_1 + x_2 + x_3 = 0\}$, with the six short roots $\pm(\varepsilon_i - \varepsilon_j)$ of square length $2$ and the six long roots $\pm(2\varepsilon_i - \varepsilon_j - \varepsilon_k)$, $\{i, j, k\} = \{1, 2, 3\}$, of square length $6$. Take $\alpha_1 = \varepsilon_1 - \varepsilon_2$ (short) and $\alpha_2 = -2\varepsilon_1 + \varepsilon_2 + \varepsilon_3$ (long). Then $\alpha_1 \cdot \alpha_2 = -3$, so $p_{12} = 2(-3)/6 = -1$ and $p_{21} = 2(-3)/2 = -3$, and $c_{12} = 3$, an angle of $150$ degrees. Check one reflection: $s_2(\alpha_1) = \alpha_1 - p_{12}\alpha_2 = \alpha_1 + \alpha_2 = \varepsilon_3 - \varepsilon_1$, a short root. The Weyl group is dihedral of order $12$.

**Counterexample (Coxeter weight four, independent roots).** On $M = \mathbb{Q}^2$ take $x = \varepsilon_1$, $f = 2\varepsilon_1^* - 2\varepsilon_2^*$, $y = \varepsilon_2$, $g = -2\varepsilon_1^* + 2\varepsilon_2^*$. Then $f(x) = g(y) = 2$ and $f(y) g(x) = (-2)(-2) = 4$, while $x$ and $y$ are independent. Here $v = -2\varepsilon_1 - 2\varepsilon_2$, and the orbit $\varepsilon_2 - 2n(\varepsilon_1 + \varepsilon_2)$ is infinite. This is the affine root system $\tilde{A}_1$.

### The library around it

::: mathlib
`RootPairing` · `Mathlib.LinearAlgebra.RootSystem.Defs`

`RootPairing ι R M N` extends `M →ₗ[R] N →ₗ[R] R` with `IsPerfPair`, and has the fields `root : ι ↪ M`, `coroot : ι ↪ N`, `root_coroot_two`, `reflectionPerm`, `reflectionPerm_root` and `reflectionPerm_coroot`. `P.pairing i j` is `P.toLinearMap (P.root i) (P.coroot j)`, and `P.reflection i` is a linear equivalence of `M`. `IsRootSystem` is a class with `span_root_eq_top` and `span_coroot_eq_top`, `RootDatum` is the abbreviation for `R = ℤ`, and `P.flip` exchanges the roles of `M` and `N`.

<?decl RootPairing?>
:::

::: mathlib
`Module.infinite_range_reflection_reflection_iterate_iff` · `Mathlib.LinearAlgebra.Reflection`

`Module.reflection h` takes a proof `h : f x = 2` and gives `M ≃ₗ[R] M`. This lemma is the infinite orbit theorem, under `[HasUniqueDiv M]`. The general formula for `(reflection hf * reflection hg) ^ m` is `reflection_mul_reflection_pow_apply`, with Chebyshev polynomials evaluated at `f y * g x - 2`. The theorem on a common root is the source of `injOn_dualMap_subtype_span_range_range`.

<?decl Module.infinite_range_reflection_reflection_iterate_iff?>
:::

::: mathlib
`RootPairing.mk''` · `Mathlib.LinearAlgebra.RootSystem.Basic`

The constructor of the corollary: over a field of characteristic $0$ with finite `ι`, it needs only `p (root i) (coroot i) = 2`, pre-reflections that map the roots into the roots, and roots that span. `isRootSystem_mk''` adds integrality and gives `IsRootSystem`. `RootPairing.ext` says that, over a domain of characteristic $0$, the pairing, the roots and the set of coroots determine the root pairing.

<?decl RootPairing.mk''?>
:::

::: mathlib
`RootPairing.weylGroup` · `Mathlib.LinearAlgebra.RootSystem.WeylGroup`

`P.weylGroup` is `Subgroup.closure (range (Equiv.reflection P))` inside `Aut P`. A morphism `RootPairing.Hom P Q` has the fields `weightMap`, `coweightMap`, `indexEquiv`, `weight_coweight_transpose`, `root_weightMap` and `coroot_coweightMap`. `weylGroupToPerm` is the action on `ι`.

<?decl RootPairing.weylGroup?>
:::

::: mathlib
`RootPairing.coxeterWeight_eq_four_iff_not_linearIndependent` · `Mathlib.LinearAlgebra.RootSystem.Reduced`

The theorem on Coxeter weight four, with `[Finite ι] [CharZero R] [IsDomain R] [Module.IsTorsionFree R M]`. `IsReduced` has the single field `eq_or_eq_neg`, and `pairing_two_two_iff` shows that $p_{ij} = p_{ji} = 2$ forces $i = j$.

<?decl RootPairing.coxeterWeight_eq_four_iff_not_linearIndependent?>
:::

::: mathlib
`RootPairing.ofBilinear` · `Mathlib.LinearAlgebra.RootSystem.OfBilinear`

`ofBilinear B hNB hSB h2` is indexed by the subtype `{x | B.IsReflective x}` and pairs `M` with `Dual R M`. It needs `[IsReflexive R M]`, a nondegenerate symmetric `B` and `IsRegular (2 : R)`.

<?decl RootPairing.ofBilinear?>
:::

::: mathlib
`RootPairing.IsCrystallographic` · `Mathlib.LinearAlgebra.RootSystem.IsValuedIn`

`IsCrystallographic` is `IsValuedIn ℤ`, and `pairingIn S i j` is the chosen value in `S`. In `BaseChange`, `restrictScalarsRat` turns a balanced crystallographic root pairing over a field of characteristic $0$ into a root system over $\mathbb{Q}$ on the $\mathbb{Q}$-spans of the roots and coroots.

<?decl RootPairing.IsCrystallographic?>
:::

`RootPairingCat` bundles root pairings over a fixed ring into a type. `IsIrreducible` has the four fields of the definition, and `isSimpleModule_weylGroupRootRep_iff` relates the condition on `M` to simplicity of `weylGroupRootRep`.

Common errors of a learner: The first error is to read `P.pairing i j` as $\langle \alpha_j, \alpha_i^\vee \rangle$; it is $\langle \alpha_i, \alpha_j^\vee \rangle$, so `reflectionPerm_root` subtracts `P.pairing j i • P.root i` from `P.root j`. The second error is to expect `RootPairing` to include the spanning condition; it does not, and `IsRootSystem` is a separate class. The third error is to forget that `root` is an embedding `ι ↪ M`: the roots are indexed, and the set of roots is `range P.root`. The fourth error is to look for the Weyl group in `M ≃ₗ[R] M`; it lives in `Aut P`.

### Exercises

1. (A) In $A_2$, compute $s_1 s_2$ on $\alpha_1$ and $\alpha_2$ and show that it has order $3$. Hint: $s_1 s_2(\alpha_1) = \alpha_2$ and $s_1 s_2(\alpha_2) = -\alpha_1 - \alpha_2$.
2. (A) List the eight roots of $B_2$ with their coroots, and check that the coroots form a root system of type $B_2$ with long and short exchanged. Hint: $(\pm\varepsilon_1)^\vee = \pm 2\varepsilon_1$.
3. (B) Show that the root system $A_1 \times A_1$ with roots $\pm\varepsilon_1$, $\pm\varepsilon_2$ in $\mathbb{Q}^2$ is reduced but not irreducible. Hint: the line $\mathbb{Q}\varepsilon_1$ is stable under both reflections.
4. (B) Show that the roots $\pm\varepsilon_1$, $\pm 2\varepsilon_1$ in $\mathbb{Q}$ form a root system $BC_1$ that is not reduced, and compute $c_{ij}$ for $\alpha_i = \varepsilon_1$, $\alpha_j = 2\varepsilon_1$. Hint: the answer is $4$, as the theorem predicts.
5. (B) Let $u = s_i s_j$ in a root pairing with $c_{ij} = 1$. Show that $u^3 = 1$ on the span of $\alpha_i$ and $\alpha_j$. Hint: in the basis $\alpha_i, \alpha_j$, $u$ has trace $c_{ij} - 2 = -1$ and determinant $1$.
6. (C) Let $B$ be the form of the lattice $\mathbb{Z}^2$ with $B(x, y) = x \cdot y$. Find all reflective vectors and show that they form the non-reduced root system $BC_2$ with $12$ roots. Hint: $x \cdot x$ must divide $2x_1$ and $2x_2$; for $x = (a, 0)$ this means $a \mid 2$, and the answer is $\pm\varepsilon_i$, $\pm 2\varepsilon_i$ and $\pm\varepsilon_1 \pm \varepsilon_2$.

### Notes and history

Root systems arose in the classification of complex simple Lie algebras by Killing and Cartan, and Coxeter classified the finite reflection groups in 1934. Root data, with roots and coroots in dual lattices, classify reductive algebraic groups. Mathlib takes this form as primary and indexes the roots by a type, so that the bijection between roots and coroots is not a dependent function.

The Mathlib files are by these authors, read from their headers: `Reflection` by Oliver Nash, Deepro Choudhury, Mitchell Lee and Johan Commelin; `RootSystem.Defs` and `RootSystem.Basic` by Oliver Nash, Deepro Choudhury and Scott Carnahan; `RootSystem.Hom`, `RootSystem.WeylGroup`, `RootSystem.OfBilinear` and `RootSystem.RootPairingCat` by Scott Carnahan; `RootSystem.Reduced` by Oliver Nash and Scott Carnahan; `RootSystem.IsValuedIn` by Scott Carnahan and Oliver Nash; `RootSystem.Irreducible` and `RootSystem.BaseChange` by Oliver Nash.

### Reference

<?reference?>
