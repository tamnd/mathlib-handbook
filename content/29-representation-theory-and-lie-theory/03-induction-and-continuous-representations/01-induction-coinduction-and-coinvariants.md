---
title: Induction, coinduction and coinvariants
kind: theory
modules:
  - Mathlib.RepresentationTheory.Coinvariants
  - Mathlib.RepresentationTheory.Induced
  - Mathlib.RepresentationTheory.Coinduced
  - Mathlib.RepresentationTheory.FiniteIndex
  - Mathlib.RepresentationTheory.Stabilizer
  - Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
explains:
  E3: [Representation.Coinvariants, Representation.Coinvariants.lift, Rep.coinvariantsAdjunction, Representation.coinvariantsTprodLeftRegularLEquiv, Representation.IndV, Representation.ind, Rep.indResAdjunction, Representation.coindV, Representation.coind, Rep.resCoindAdjunction, Rep.indCoindIso, Representation.stabilizer_conj, IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed, IsSimpleModule.finrank_eq_one_of_isMulCommutative]
  E2: [Representation.Coinvariants.ker, Representation.Coinvariants.mk, Representation.Coinvariants.mk_eq_iff, Representation.Coinvariants.mk_self_apply, Representation.Coinvariants.lift_mk, Representation.Coinvariants.hom_ext, Representation.Coinvariants.map, Representation.coinvariantsFinsuppLEquiv, Representation.toCoinvariants, Representation.quotientToCoinvariants, Rep.coinvariantsFunctor, Rep.desc, Rep.coinvariantsTensor, Rep.coinvariantsShortComplex_shortExact, Representation.IndV.mk, Representation.ind_mk, Rep.ind, Rep.indFunctor, Rep.indResHomEquiv, Rep.coinvariantsTensorIndNatIso, Representation.mem_coindV, Representation.coind', Rep.coind, Rep.coindFunctor, Rep.coindVEquiv, Rep.coindIso, Rep.resCoindToHom, Rep.resCoindHomEquiv, Rep.indToCoindAux, Rep.indToCoind, Rep.coindToInd, Rep.indCoindNatIso, Rep.resIndAdjunction, Rep.coindResAdjunction, Representation.stabilizer, Representation.mem_stabilizer, Representation.stabilizer_zero, Representation.le_stabilizer_smul, Representation.le_stabilizer_add, Representation.le_stabilizer_sum, Representation.IntertwiningMap.stabilizer_le]
  E1: auto
families: []
requires: [V05.C04, V05.C05, V05.C06, V07.C01, V08.C02, V24.C05, V26.C07, V26.C08, V29.C01, V29.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Induction, coinduction and coinvariants

### Overview

A group homomorphism $\varphi \colon G \to H$ gives the restriction functor $\mathrm{Res}_\varphi$ from representations of $H$ to representations of $G$: the group $G$ acts on an $H$-representation $B$ through $\varphi$. Restriction has a left adjoint, induction, and a right adjoint, coinduction. These two adjunctions are Frobenius reciprocity. When $\varphi$ is the inclusion of a subgroup of finite index, induction and coinduction agree. For an infinite index they differ, and both are needed: coinduction is the tool of Shapiro's lemma in group cohomology, and induction is the tool of Shapiro's lemma in group homology (Volume 26, Chapter 8).

Mathlib builds induction from coinvariants, the largest quotient of $V$ on which $G$ acts trivially, so the section starts there. It then treats induction, coinduction, the two adjunctions and the finite index isomorphism. Two short topics close it: stabilizers of vectors, and Schur's lemma for a simple module over a $k$-algebra.

Throughout, $k$ is a commutative ring, $G$ and $H$ are groups, $\varphi \colon G \to H$ is a homomorphism, and $(A, \rho)$ is a $k$-linear representation of $G$ in the sense of Chapter 1. The notation $k[H]$ is the group algebra, and $[h]$ is its basis element at $h \in H$.

### Definitions

**Definition (Coinvariants).** Let $I_G V \subseteq V$ be the $k$-submodule spanned by the elements $\rho(g)x - x$ for $g \in G$ and $x \in V$. The coinvariants of $\rho$ are the quotient $V_G = V / I_G V$, and $[x]$ is the class of $x$.

A $k$-linear map $f \colon V \to W$ factors through $V_G$ if and only if $f \circ \rho(g) = f$ for each $g$. Invariants $V^G$ are the largest subrepresentation with trivial action, and coinvariants are the largest quotient with trivial action.

**Definition (Induced representation).** The group $G$ acts on $k[H]$ by $g \cdot [h] = [\varphi(g)h]$. The induced module is
$$\mathrm{Ind}_\varphi A = \big(k[H] \otimes_k A\big)_G,$$
the coinvariants of the diagonal action $g \cdot ([h] \otimes a) = [\varphi(g)h] \otimes \rho(g)a$. Write $\langle h, a \rangle$ for the class of $[h] \otimes a$. The group $H$ acts on $\mathrm{Ind}_\varphi A$ by $h' \cdot \langle h, a \rangle = \langle h h'^{-1}, a \rangle$.

The relation in the quotient is $\langle \varphi(g)h, \rho(g)a \rangle = \langle h, a \rangle$. The action of $h'$ is well defined, because right multiplication by $h'^{-1}$ commutes with left multiplication by $\varphi(g)$.

**Definition (Coinduced representation).** The coinduced module is
$$\mathrm{Coind}_\varphi A = \{ f \colon H \to A \mid f(\varphi(g)h) = \rho(g) f(h) \text{ for all } g \in G,\ h \in H \},$$
and $H$ acts on it by right translation: $(h' \cdot f)(h) = f(h h')$.

Right translation keeps the defining condition, because $(h' \cdot f)(\varphi(g)h) = f(\varphi(g)hh') = \rho(g)f(hh')$. The functions need not have finite support.

**Definition (Stabilizer).** The stabilizer of $v \in V$ is the subgroup $\mathrm{Stab}(v) = \{ g \in G \mid \rho(g)v = v \}$.

It is a subgroup, since $\rho$ is a homomorphism and $\rho(g)v = v$ gives $v = \rho(g^{-1})v$.

### Theorems and proofs

**Proposition (Coinvariants are left adjoint to the trivial action).** For a representation $A$ of $G$ and a $k$-module $B$ with the trivial action, there is a natural bijection
$$\mathrm{Hom}_k(A_G, B) \cong \mathrm{Hom}_G(A, B).$$

*Proof.* A $G$-map $f \colon A \to B$ satisfies $f(\rho(g)x) = g \cdot f(x) = f(x)$, since $G$ acts trivially on $B$. So $f$ vanishes on each generator $\rho(g)x - x$ of $I_G A$, hence on $I_G A$, and $f$ factors as $\bar f \circ [\,\cdot\,]$ for a unique $k$-linear $\bar f \colon A_G \to B$. Conversely, for a $k$-linear $\bar f \colon A_G \to B$ the composite $\bar f \circ [\,\cdot\,]$ is a $G$-map, because $[\rho(g)x] = [x]$. These are inverse, since $[\,\cdot\,]$ is surjective. $\square$

**Proposition (Coinvariants of a tensor product with the regular representation).** For any representation $(V, \rho)$ of $G$, the map $[v \otimes [g]] \mapsto \rho(g^{-1})v$ is an isomorphism $(V \otimes_k k[G])_G \cong V$, where $G$ acts diagonally.

*Proof.* The bilinear map $(v, [g]) \mapsto \rho(g^{-1})v$ is constant on orbits: the element $g'$ sends $v \otimes [g]$ to $\rho(g')v \otimes [g'g]$, and $\rho((g'g)^{-1})\rho(g')v = \rho(g^{-1})v$. So it defines $\Phi \colon (V \otimes k[G])_G \to V$. Let $\Psi(v) = [v \otimes [1]]$. Then $\Phi\Psi(v) = v$. For the other composite, apply the relation with $g' = g^{-1}$: $[v \otimes [g]] = [\rho(g^{-1})v \otimes [1]] = \Psi\Phi([v \otimes [g]])$. These elements span the quotient, so $\Psi\Phi = \mathrm{id}$. $\square$

**Theorem (Frobenius reciprocity for induction).** For representations $A$ of $G$ and $B$ of $H$, the map $F \mapsto F(\langle 1, \cdot \rangle)$ is a bijection
$$\mathrm{Hom}_H(\mathrm{Ind}_\varphi A, B) \cong \mathrm{Hom}_G(A, \mathrm{Res}_\varphi B),$$
natural in $A$ and $B$. So induction is left adjoint to restriction.

*Proof.* Let $F$ be an $H$-map and $\psi(a) = F(\langle 1, a\rangle)$. Then $\psi(\rho(g)a) = F(\langle 1, \rho(g) a\rangle) = F(\langle \varphi(g)^{-1}, a\rangle)$ by the relation, and $\langle \varphi(g)^{-1}, a \rangle = \varphi(g) \cdot \langle 1, a\rangle$. So $\psi(\rho(g)a) = \varphi(g) \cdot \psi(a)$, and $\psi$ is a $G$-map to $\mathrm{Res}_\varphi B$.

Conversely, let $\psi \colon A \to \mathrm{Res}_\varphi B$ be a $G$-map, and define $F(\langle h, a\rangle) = h^{-1} \cdot \psi(a)$. This respects the relation: $F(\langle \varphi(g)h, \rho(g)a\rangle) = h^{-1}\varphi(g)^{-1} \cdot \varphi(g) \cdot \psi(a) = h^{-1} \cdot \psi(a)$. It is an $H$-map: $F(h' \cdot \langle h, a\rangle) = F(\langle hh'^{-1}, a\rangle) = h' h^{-1} \cdot \psi(a) = h' \cdot F(\langle h, a \rangle)$. The value $F(\langle 1, a\rangle) = \psi(a)$ recovers $\psi$. An $H$-map is fixed by its values on the elements $\langle 1, a\rangle$, because $\langle h, a\rangle = h^{-1} \cdot \langle 1, a\rangle$. So the two maps are inverse. $\square$

**Theorem (Frobenius reciprocity for coinduction).** For representations $B$ of $H$ and $A$ of $G$, there is a natural bijection
$$\mathrm{Hom}_G(\mathrm{Res}_\varphi B, A) \cong \mathrm{Hom}_H(B, \mathrm{Coind}_\varphi A),$$
which sends $f$ to the map $b \mapsto (h \mapsto f(h \cdot b))$. So coinduction is right adjoint to restriction.

*Proof.* Let $f$ be a $G$-map and $F(b)(h) = f(h \cdot b)$. The function $F(b)$ lies in the coinduced module: $F(b)(\varphi(g)h) = f(\varphi(g) h \cdot b) = \rho(g) f(h \cdot b)$, because $f$ is a $G$-map. The map $F$ is an $H$-map: $(h' \cdot F(b))(h) = F(b)(hh') = f(hh' \cdot b) = F(h' \cdot b)(h)$. In the other direction, an $H$-map $F$ gives $f(b) = F(b)(1)$. It is a $G$-map: $f(\varphi(g) \cdot b) = F(\varphi(g)\cdot b)(1) = F(b)(\varphi(g)) = \rho(g)F(b)(1)$. The composites are the identity: $F(b)(h) = (h \cdot F(b))(1) = F(h\cdot b)(1)$ shows that $F$ is fixed by $f$, and $f(1 \cdot b) = f(b)$ gives the other composite. $\square$

**Theorem (Induction equals coinduction in finite index).** Let $S \le G$ be a subgroup of finite index, and let $A$ be a representation of $S$. Then $\mathrm{Ind}_S^G A \cong \mathrm{Coind}_S^G A$ as representations of $G$.

*Proof.* Define $\alpha \colon \mathrm{Ind}\,A \to \mathrm{Coind}\,A$ on generators: $\alpha\langle g, a\rangle$ is the function supported on the right coset $Sg$ with value $\rho(s)a$ at $sg$. It lies in $\mathrm{Coind}$: at $s'sg$ it takes the value $\rho(s's)a = \rho(s')\rho(s)a$. It respects the relation: the function $\alpha\langle sg, \rho(s)a\rangle$ is supported on $Ssg = Sg$ and takes at $s_1 g = (s_1 s^{-1})sg$ the value $\rho(s_1 s^{-1})\rho(s)a = \rho(s_1)a$. It is a $G$-map: $g' \cdot \langle g, a\rangle = \langle g g'^{-1}, a\rangle$ maps to the function supported on $Sgg'^{-1}$ with value $\rho(s)a$ at $sgg'^{-1}$, and the right translate $x \mapsto \alpha\langle g, a\rangle(xg')$ is the same function.

Choose representatives $g_1, \dots, g_n$ of the right cosets, and define $\beta(f) = \sum_i \langle g_i, f(g_i)\rangle$. A change of representative $g_i \mapsto sg_i$ changes the term to $\langle sg_i, \rho(s) f(g_i)\rangle$, which is the same class. For a generator, $\alpha\langle g, a \rangle$ vanishes off $Sg$, so $\beta\alpha\langle g, a\rangle = \langle s_0g, \rho(s_0)a\rangle = \langle g, a \rangle$, where $g_j = s_0 g$ is the representative of $Sg$. For $f \in \mathrm{Coind}\,A$, the summand $\alpha\langle g_i, f(g_i)\rangle$ is the function on $Sg_i$ with value $\rho(s)f(g_i) = f(sg_i)$ at $sg_i$. The sum over $i$ is $f$. So $\alpha\beta = \mathrm{id}$, and $\alpha$ is an isomorphism. $\square$

**Corollary (Two more adjunctions).** For $S$ of finite index, induction is also right adjoint to restriction and coinduction is also left adjoint to restriction.

*Proof.* Replace $\mathrm{Ind}$ by the isomorphic $\mathrm{Coind}$ in the first reciprocity theorem, and $\mathrm{Coind}$ by $\mathrm{Ind}$ in the second. The isomorphism is natural in $A$, since $\alpha$ has the same formula for each $A$. $\square$

**Proposition (Stabilizers of translates).** For $g \in G$ and $v \in V$, $\mathrm{Stab}(\rho(g)v) = g\,\mathrm{Stab}(v)\,g^{-1}$. For a $G$-map $f \colon V \to W$, $\mathrm{Stab}(v) \le \mathrm{Stab}(f(v))$.

*Proof.* An element $x$ fixes $\rho(g)v$ if and only if $\rho(g^{-1}xg)v = v$, that is, $g^{-1}xg \in \mathrm{Stab}(v)$, that is, $x \in g\,\mathrm{Stab}(v)\,g^{-1}$. If $\rho(x)v = v$ then $\rho'(x)f(v) = f(\rho(x)v) = f(v)$. $\square$

**Theorem (Schur's lemma for algebras).** Let $k$ be an algebraically closed field, let $A$ be a $k$-algebra, and let $V$ be a simple $A$-module that is finite dimensional over $k$. Then each $A$-linear endomorphism of $V$ is a scalar, and $k \to \mathrm{End}_A(V)$ is bijective. If $A$ is commutative, then $\dim_k V = 1$.

*Proof.* Let $\theta \in \mathrm{End}_A(V)$. The module $V$ is nonzero and finite dimensional over the algebraically closed field $k$, so $\theta$ has an eigenvalue $\lambda$. The map $\theta - \lambda$ is $A$-linear, so its kernel is a nonzero $A$-submodule. Since $V$ is simple, the kernel is $V$, and $\theta = \lambda$. This gives surjectivity. The map $\lambda \mapsto \lambda \cdot \mathrm{id}$ is injective because $V \ne 0$. If $A$ is commutative, each $a \in A$ acts by an $A$-linear map, which is a scalar. So each $k$-line $kv$ with $v \ne 0$ is an $A$-submodule. Simplicity gives $kv = V$, and $\dim_k V = 1$. $\square$

For $A = k[G]$ with $G$ abelian, an irreducible finite dimensional complex representation is a character.

### Examples

**Example (Induction from the trivial subgroup).** Let $\varphi \colon 1 \to G$ and $A = k$. Then $\mathrm{Ind}\,k = (k[G] \otimes k)_1 = k[G]$, with $h' \cdot [h] = [hh'^{-1}]$. The map $[h] \mapsto [h^{-1}]$ is an isomorphism with the left regular representation, since $hh'^{-1}$ goes to $h'h^{-1}$. The coinduced module is the module of all functions $G \to k$ with right translation. For $G = \mathbb{Z}$ the two differ: the constant function $1$ is a nonzero invariant of $\mathrm{Coind}\,k$, but a finite sum $\sum c_n [n]$ fixed by translation by $1$ has $c_n = c_{n+1}$ for all $n$, so it is $0$. So the finite index hypothesis of the theorem cannot be dropped.

**Example (Inducing a character of $A_3$ to $S_3$).** Let $c = (1\,2\,3)$, let $\tau = (1\,2)$, and let $\chi$ be the character of $A_3 = \langle c\rangle$ with $\chi(c) = \omega = e^{2\pi i/3}$. Use the coinduced model, which is isomorphic by the finite index theorem. A function $f$ with $f(sx) = \chi(s)f(x)$ is fixed by $f(1)$ and $f(\tau)$, so the space has dimension $2 = [S_3 : A_3]$. Compute with $\tau c = c^{-1}\tau$:
$$(c \cdot f)(1) = f(c) = \omega f(1), \qquad (c \cdot f)(\tau) = f(\tau c) = f(c^{-1}\tau) = \omega^2 f(\tau).$$
Also $(\tau \cdot f)(1) = f(\tau)$ and $(\tau \cdot f)(\tau) = f(1)$. In the basis given by $f(1)$ and $f(\tau)$, $c$ acts by $\mathrm{diag}(\omega, \omega^2)$ and $\tau$ swaps the two coordinates. The character takes the values $2$, $0$ and $\omega + \omega^2 = -1$ at $1$, $\tau$ and $c$. This is the irreducible representation of dimension $2$ of Chapter 2. A direct check: a $c$-stable line is one of the two eigenlines, since $\omega \ne \omega^2$, and $\tau$ swaps them. For the trivial character, $c = \mathrm{id}$ and $\tau$ is a swap: the sum of the trivial and sign representations.

**Example (Stabilizers in the permutation representation).** Let $S_3$ permute the basis $e_1, e_2, e_3$ of $\mathbb{C}^3$. Then $\mathrm{Stab}(e_3) = \{1, (1\,2)\}$ and $\mathrm{Stab}(e_1 + e_2 + e_3) = S_3$. The element $c = (1\,2\,3)$ sends $e_3$ to $e_1$, and $\mathrm{Stab}(e_1) = c\{1,(1\,2)\}c^{-1} = \{1, (2\,3)\}$, as the proposition predicts. The intersection $\mathrm{Stab}(e_1) \cap \mathrm{Stab}(e_2) = 1$ is contained in $\mathrm{Stab}(e_1 + e_2) = \{1, (1\,2)\}$, and the containment is strict.

**Example (Coinvariants of the permutation representation).** For the same representation, $I_G V$ is spanned by the differences $e_i - e_j$, so $V_G \cong \mathbb{C}$ through $x \mapsto x_1 + x_2 + x_3$. For $\mathbb{Z}/2$ acting on $\mathbb{Z}$ by $-1$, $I_G V = 2\mathbb{Z}$, so the coinvariants are $\mathbb{Z}/2$ and the invariants are $0$.

### The library around it

::: mathlib
`Representation.Coinvariants` · `Mathlib.RepresentationTheory.Coinvariants`

`Coinvariants.ker ρ` is the span of the elements `ρ g x - x`, and `Coinvariants ρ` is the quotient by it. `Coinvariants.mk ρ` is the quotient map, `mk_eq_iff` describes its fibres and `mk_self_apply` is the relation `mk (ρ g x) = mk x`. `Coinvariants.lift f h` needs `h : ∀ g, f ∘ₗ ρ g = f`, and `lift_mk` and `hom_ext` give the universal property. `Coinvariants.map` is the functoriality. `coinvariantsFinsuppLEquiv` commutes coinvariants with direct sums, and `coinvariantsTprodLeftRegularLEquiv` is the second proposition. For a normal subgroup `S`, `toCoinvariants` and `quotientToCoinvariants` make `A_S` a representation of `G` and of `G ⧸ S`.

<?decl Representation.coinvariantsTprodLeftRegularLEquiv?>
:::

::: mathlib
`Rep.coinvariantsAdjunction` · `Mathlib.RepresentationTheory.Coinvariants`

`Rep.coinvariantsFunctor k G : Rep k G ⥤ ModuleCat k` and `coinvariantsAdjunction k G : coinvariantsFunctor k G ⊣ trivialFunctor k G` are the first proposition in categorical form. `Rep.coinvariantsTensor` is the bifunctor $(A, B) \mapsto (A \otimes B)_G$, and `coinvariantsShortComplex_shortExact` is the exact sequence $0 \to \ker \to A \to A_S \to 0$ for a normal subgroup `S`.

<?decl Rep.coinvariantsAdjunction?>
:::

::: mathlib
`Rep.indResAdjunction` · `Mathlib.RepresentationTheory.Induced`

`Representation.IndV φ ρ` is the coinvariants of `tprod ((leftRegular k H).comp φ) ρ` on `k[H] ⊗[k] A`, and `IndV.mk φ ρ h` is the map $a \mapsto \langle h, a\rangle$. `Representation.ind φ ρ` is the action of `H`, and `ind_mk` says `ind φ ρ h₁ (IndV.mk _ _ h₂ a) = IndV.mk _ _ (h₂ * h₁⁻¹) a`. `Rep.ind φ A` and `Rep.indFunctor k φ` are the categorical forms. `indResHomEquiv` is the bijection of the theorem, with `f ↦ f ∘ IndV.mk 1`, and `indResAdjunction k φ : indFunctor k φ ⊣ resFunctor φ` is the adjunction. `coinvariantsTensorIndNatIso` gives $(\mathrm{Ind}\,A \otimes B)_H \cong (A \otimes \mathrm{Res}\,B)_G$, the input of Shapiro's lemma for homology.

<?decl Rep.indResAdjunction?>
:::

::: mathlib
`Rep.resCoindAdjunction` · `Mathlib.RepresentationTheory.Coinduced`

`Representation.coindV φ σ` is the submodule of `H → A` cut out by `f (φ g * h) = σ g (f h)`, as `mem_coindV` states, and `Representation.coind` acts by right translation. `Representation.coind'` is a second model by `Hom` from the restricted regular representation, compared by `Rep.coindVEquiv` and `Rep.coindIso`. `Rep.resCoindToHom` is the map $b \mapsto (h \mapsto f(h \cdot b))$ of the proof, `resCoindHomEquiv` is the bijection and `resCoindAdjunction k φ : resFunctor φ ⊣ coindFunctor k φ` is the adjunction. This file works for monoids, not only groups.

<?decl Rep.resCoindAdjunction?>
:::

::: mathlib
`Rep.indCoindIso` · `Mathlib.RepresentationTheory.FiniteIndex`

The file takes `[DecidableRel (QuotientGroup.rightRel S)]` and `[S.FiniteIndex]`. `indToCoindAux A g` is the function supported on `S g`, and `indToCoindAux_self`, `indToCoindAux_of_not_rel` and `indToCoindAux_mul_snd` are the checks of the proof. `indToCoind` and `coindToInd` are $\alpha$ and $\beta$, the latter a sum over `Quotient (QuotientGroup.rightRel S)`. `indCoindIso A` is the theorem, `indCoindNatIso` its natural form, and `resIndAdjunction` and `coindResAdjunction` are the corollary.

<?decl Rep.indCoindIso?>
:::

::: mathlib
`IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed` · `Mathlib.RepresentationTheory.AlgebraRepresentation.Basic`

The hypotheses are `[IsSimpleModule A V] [FiniteDimensional k V] [IsAlgClosed k]` with `[IsScalarTower k A V]`. The Mathlib proof differs from the text: it shows that `Module.End A V` is a finite dimensional division algebra over `k` and uses that such an algebra over an algebraically closed field is `k`. `finrank_eq_one_of_isMulCommutative` is the commutative case. The stabilizer lemmas live in `Mathlib.RepresentationTheory.Stabilizer`: `stabilizer`, `mem_stabilizer`, `stabilizer_zero`, `le_stabilizer_smul`, `le_stabilizer_add`, `le_stabilizer_sum`, `IntertwiningMap.stabilizer_le` and `stabilizer_conj`, which uses `MulAut.conj g`.

<?decl IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed?>
:::

Common errors of a learner: The first error is to expect the induced representation to be `k[H] ⊗[k[G]] A`. Mathlib uses the coinvariants of `k[H] ⊗[k] A`, and the action of `h` multiplies on the right by `h⁻¹`, so a computation must follow `ind_mk` and not a textbook formula. The second error is to use `indCoindIso` without its instances: it needs `S.FiniteIndex` and a decidable right coset relation, and it does not apply to a general homomorphism `φ`, only to `S.subtype`. The third error is to confuse `Coinvariants` with `invariants`; the first is a quotient module, the second a submodule, and for $\mathbb{Z}/2$ acting by $-1$ on $\mathbb{Z}$ they are $\mathbb{Z}/2$ and $0$.

### Exercises

1. (A) Compute the coinvariants of $\mathbb{Z}/n$ acting on $k[\mathbb{Z}/n]$ by the regular representation. Hint: the map $\sum c_g [g] \mapsto \sum c_g$ is the quotient map.
2. (A) Show that $\mathrm{Stab}(c\,v) \supseteq \mathrm{Stab}(v)$ for $c \in k$, and give an example in which the containment is strict. Hint: take $c = 0$.
3. (A) Compute $\mathrm{Ind}_{\langle \tau \rangle}^{S_3}$ of the sign character of $\langle \tau\rangle$, with $\tau = (1\,2)$. Find its dimension and its character. Hint: the index is $3$; use the coinduced model and three coset representatives.
4. (B) Prove transitivity of induction: for $K \le H \le G$, $\mathrm{Ind}_H^G \mathrm{Ind}_K^H A \cong \mathrm{Ind}_K^G A$. Hint: both functors are left adjoint to $\mathrm{Res}_K^G$, and adjoints are unique up to isomorphism.
5. (B) Show that $\mathrm{Ind}_\varphi$ preserves direct sums and that $\mathrm{Coind}_\varphi$ preserves products. Hint: left adjoints preserve colimits and right adjoints preserve limits.
6. (B) Let $S \le G$ be normal. Show that $A \mapsto A_S$ is left adjoint to inflation from representations of $G/S$ to representations of $G$. Hint: a $G$-map $A \to B$ to a representation on which $S$ acts trivially is constant on $S$-orbits.
7. (C) Prove the Mackey formula for $S, T \le G$ of finite index: $\mathrm{Res}_T \mathrm{Ind}_S A \cong \bigoplus_{TgS} \mathrm{Ind}_{T \cap gSg^{-1}}^{T} ({}^g A)$, with one summand for each double coset. Hint: split the coinduced functions by their support on the double cosets.

### Notes and history

Frobenius created the theory of group characters in 1896, and soon after he introduced induced characters and the reciprocity law that carries his name. The modern statement as a pair of adjunctions comes from the module theoretic view of representations and from category theory. Mackey extended induction to infinite and topological groups, and the double coset formula of Exercise 7 carries his name. The form of Schur's lemma for an algebraically closed field is the input of the character theory of Chapter 2.

The Mathlib files are by these authors, read from their headers: `Coinvariants`, `Induced`, `Coinduced` and `FiniteIndex` by Amelia Livingston; `Stabilizer` by Jiaxi Mo; `AlgebraRepresentation.Basic` by Stepan Nesterov.

### Reference

<?reference?>
