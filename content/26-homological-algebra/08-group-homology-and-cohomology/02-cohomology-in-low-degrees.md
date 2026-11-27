---
title: Cohomology in low degrees
kind: theory
modules:
  - Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
  - Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
  - Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
explains:
  E3: [groupCohomology.H0Iso, groupCohomology.mem_cocycles₁_iff, groupCohomology.H1IsoOfIsTrivial, groupCohomology.H1π_eq_zero_iff, groupCohomology.mem_cocycles₂_iff, groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units, groupCohomology.H1ofAutOnUnitsUnique, groupCohomology.exists_div_of_norm_eq_one, groupHomology.H0Iso, groupHomology.H1AddEquivOfIsTrivial]
  E2: [groupCohomology.d₀₁, groupCohomology.d₁₂, groupCohomology.d₂₃, groupCohomology.d₀₁_ker_eq_invariants, groupCohomology.cocycles₁, groupCohomology.cocycles₂, groupCohomology.coboundaries₁, groupCohomology.coboundaries₂, groupCohomology.IsCocycle₁, groupCohomology.IsCocycle₂, groupCohomology.IsCoboundary₁, groupCohomology.IsCoboundary₂, groupCohomology.IsMulCocycle₁, groupCohomology.IsMulCoboundary₁, groupCohomology.map_one_of_isCocycle₁, groupCohomology.map_one_fst_of_isCocycle₂, groupCohomology.map_one_snd_of_isCocycle₂, groupCohomology.cocycles₁_map_one, groupCohomology.cocycles₁_map_inv, groupCohomology.H0, groupCohomology.H1, groupCohomology.H2, groupCohomology.H0IsoOfIsTrivial, groupCohomology.H1π, groupCohomology.H1_induction_on, groupCohomology.H2π, groupCohomology.H2π_eq_zero_iff, groupCohomology.shortComplexH1, groupCohomology.isoCocycles₁, groupCohomology.coboundaries₁_eq_bot_of_isTrivial, groupCohomology.Hilbert90.aux, groupCohomology.exists_mul_galRestrict_of_norm_eq_one, groupHomology.d₁₀, groupHomology.d₂₁, groupHomology.range_d₁₀_eq_coinvariantsKer, groupHomology.cycles₁, groupHomology.boundaries₁, groupHomology.mem_cycles₁_iff, groupHomology.single_one_mem_boundaries₁, groupHomology.H0, groupHomology.H0π, groupHomology.H0IsoOfIsTrivial, groupHomology.H1, groupHomology.H1π, groupHomology.H1π_eq_zero_iff, groupHomology.mkH1OfIsTrivial, groupHomology.H1ToTensorOfIsTrivial, groupHomology.H2]
  E1: auto
families: []
requires: [V05.C05, V05.C06, V11.C01, V26.C04, V26.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Cohomology in low degrees

### Overview

The inhomogeneous complex of Section 1 is large, but in degrees $0$, $1$ and $2$ its cocycles have a direct meaning. A $0$-cocycle is an invariant element. A $1$-cocycle is a crossed homomorphism, a function $G \to A$ that is a homomorphism up to a twist by the action, and $H^1$ classifies these modulo the principal ones. A $2$-cocycle is the obstruction to splitting a group extension, and $H^2$ classifies extensions of $G$ by $A$. In homology, $H_0$ is the module of coinvariants, and $H_1(G, \mathbb{Z})$ is the abelianization of $G$.

This section proves these identifications and computes examples with cyclic groups and Galois groups. Its main theorem is Hilbert's Theorem 90 in the form of Noether: for a finite Galois extension $L/K$, $H^1(\mathrm{Gal}(L/K), L^\times) = 1$. Mathlib proves this, and deduces from it the classical statement about elements of norm $1$ in a cyclic extension. In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. The group $G$ acts on the representation $A$, and $g \cdot a$ means $\rho(g)(a)$.

### Definitions

The differentials of the inhomogeneous complex in low degrees are, by Section 1,
$$d^0 m (g) = g m - m, \qquad d^1 f (g, h) = g f(h) - f(gh) + f(g),$$
$$d^2 f (g, h, l) = g f(h, l) - f(gh, l) + f(g, hl) - f(g, h).$$

**Definition (Crossed homomorphism).** A $1$-cocycle, or crossed homomorphism, is a function $f \colon G \to A$ with $f(gh) = g f(h) + f(g)$ for all $g, h \in G$. A principal crossed homomorphism, or $1$-coboundary, is a function of the form $f(g) = gm - m$ for some $m \in A$. Write $Z^1(G, A)$ and $B^1(G, A)$ for these submodules of $\mathrm{Fun}(G, A)$, so that $H^1(G, A) = Z^1/B^1$.

**Definition (2-cocycle).** A $2$-cocycle is a function $f \colon G \times G \to A$ with
$$f(gh, l) + f(g, h) = g f(h, l) + f(g, hl)$$
for all $g, h, l$. A $2$-coboundary is a function $f(g, h) = g x(h) - x(gh) + x(g)$ for some $x \colon G \to A$. Then $H^2(G, A) = Z^2/B^2$.

**Definition (Extension).** Let $A$ be a $G$-module, written additively. An extension of $G$ by $A$ is a short exact sequence of groups $1 \to A \xrightarrow{i} E \xrightarrow{p} G \to 1$ such that conjugation in $E$ induces the given action: $e\, i(a)\, e^{-1} = i(p(e) \cdot a)$. Two extensions are equivalent if there is an isomorphism $E \cong E'$ compatible with $i$ and $p$.

**Definition (Coinvariants).** The coinvariants of $A$ are $A_G = A / I_G A$, where $I_G A$ is the submodule spanned by the elements $g a - a$.

**Definition (Multiplicative cocycle).** If $G$ acts on a multiplicative abelian group $M$, a multiplicative $1$-cocycle is a function $f \colon G \to M$ with $f(gh) = (g \cdot f(h))\, f(g)$, and it is a coboundary if $f(g) = (g \cdot \beta)/\beta$ for some $\beta \in M$.

### Theorems and proofs

**Proposition (Degree zero).** $H^0(G, A) = A^G$, the invariants, and $H_0(G, A) = A_G$, the coinvariants.

*Proof.* The complex $C^\bullet$ starts at $C^0 = A$, so $H^0 = \ker d^0 = \{m : gm = m \text{ for all } g\} = A^G$. The chain complex ends with $C_1 = \bigoplus_G A \to C_0 = A$, with $d(a[g]) = g^{-1}a - a$. The image is spanned by the elements $g^{-1} a - a$, and as $g$ runs over $G$ so does $g^{-1}$. So $H_0 = A / I_G A = A_G$. $\square$

**Proposition (Normalization of cocycles).** A $1$-cocycle satisfies $f(1) = 0$ and $f(g^{-1}) = -g^{-1} f(g)$. A $2$-cocycle satisfies $f(1, h) = f(1, 1)$ and $f(g, 1) = g f(1, 1)$.

*Proof.* Put $g = h = 1$ in the $1$-cocycle condition: $f(1) = f(1) + f(1)$, so $f(1) = 0$. Put $h = g^{-1}$: $0 = f(1) = g f(g^{-1}) + f(g)$, so $f(g^{-1}) = -g^{-1} f(g)$. For a $2$-cocycle, put $g = h = 1$: $f(1, l) + f(1, 1) = f(1, l) + f(1, l)$, so $f(1, l) = f(1, 1)$. Put $h = l = 1$: $f(g, 1) + f(g, 1) = g f(1, 1) + f(g, 1)$, so $f(g, 1) = g f(1, 1)$. $\square$

**Theorem (Degree one).** $H^1(G, A) = Z^1(G, A)/B^1(G, A)$. If $G$ acts trivially on $A$, then $H^1(G, A) \cong \mathrm{Hom}(G, A)$, the group homomorphisms from $G$ to the additive group of $A$.

*Proof.* The first statement is the definition of the cohomology of $C^\bullet$ in degree $1$: the cocycles are the kernel of $d^1$, and the coboundaries are the image of $d^0$. If the action is trivial, then $d^0 m(g) = m - m = 0$, so $B^1 = 0$, and the cocycle condition reads $f(gh) = f(h) + f(g)$, which says that $f$ is a homomorphism. $\square$

**Theorem (Degree two and extensions).** Equivalence classes of extensions of $G$ by the $G$-module $A$ correspond bijectively to $H^2(G, A)$. The split extension $A \rtimes G$ corresponds to $0$.

*Proof.* Given an extension, write $A$ as a subgroup of $E$ and choose a set-theoretic section $s \colon G \to E$ of $p$ with $s(1) = 1$. Then $s(g) s(h)$ and $s(gh)$ have the same image in $G$, so $f(g, h) = s(g) s(h) s(gh)^{-1}$ lies in $A$. Compute $s(g) s(h) s(l)$ in two ways. First, $(s(g) s(h)) s(l) = f(g, h) s(gh) s(l) = f(g, h) f(gh, l) s(ghl)$. Second, $s(g) (s(h) s(l)) = s(g) f(h, l) s(hl) = (g \cdot f(h, l))\, s(g) s(hl) = (g \cdot f(h, l))\, f(g, hl)\, s(ghl)$, where the action comes from conjugation by $s(g)$. Written additively in $A$, this is the $2$-cocycle condition. Another section has the form $s'(g) = x(g) s(g)$ with $x \colon G \to A$, and then
$$s'(g) s'(h) s'(gh)^{-1} = x(g)\, (g \cdot x(h))\, f(g, h)\, x(gh)^{-1},$$
which differs from $f$ by the coboundary $g x(h) - x(gh) + x(g)$. So the class $[f] \in H^2$ depends only on the extension, and equivalent extensions give the same class.

Conversely, given a cocycle $f$ with $f(1, 1) = 0$ (which one can arrange by subtracting the coboundary of the constant function $x(g) = f(1, 1)$), define $E_f = A \times G$ with
$$(a, g)(b, h) = (a + g b + f(g, h),\ gh).$$
The cocycle condition is exactly associativity: both $((a, g)(b, h))(c, l)$ and $(a, g)((b, h)(c, l))$ have first coordinate $a + gb + ghc$ plus the two sides of the cocycle condition. By the normalization proposition, $(0, 1)$ is the identity, and $(a, g)$ has the inverse $(-g^{-1}a - g^{-1}f(g, g^{-1}), g^{-1})$. The maps $a \mapsto (a, 1)$ and $(a, g) \mapsto g$ make $E_f$ an extension, whose class is $[f]$ for the section $g \mapsto (0, g)$. These two constructions are inverse up to equivalence. For $f = 0$, $E_0 = A \rtimes G$. $\square$

**Theorem (Homology in degree one).** If $G$ acts trivially on the abelian group $A$, then $H_1(G, A) \cong G^{\mathrm{ab}} \otimes_{\mathbb{Z}} A$. In particular $H_1(G, \mathbb{Z}) \cong G^{\mathrm{ab}}$.

*Proof.* For the trivial action, the chain differential $C_1 \to C_0$ is $d(a[g]) = a - a = 0$, so each $1$-chain is a cycle. The differential $C_2 \to C_1$ is $d(a[g, h]) = a[h] - a[gh] + a[g]$. So $H_1 = \bigoplus_G A / \langle a[g] + a[h] - a[gh] \rangle$. Consider $A = \mathbb{Z}$ first. Define $\alpha \colon H_1 \to G^{\mathrm{ab}}$ by $[g] \mapsto \bar g$. It is well defined, because $\bar g \bar h = \overline{gh}$ in $G^{\mathrm{ab}}$, written multiplicatively. Define $\beta \colon G \to H_1$ by $g \mapsto [g]$. The relation $[g] + [h] = [gh]$ says that $\beta$ is a homomorphism to the abelian group $H_1$, so it factors through $G^{\mathrm{ab}}$ by the adjunction of Chapter 7, Section 1. The maps $\alpha$ and $\bar\beta$ are inverse on generators. For general $A$, the same argument gives the map $a[g] \mapsto \bar g \otimes a$ and its inverse $\bar g \otimes a \mapsto a[g]$; the relation in $H_1$ is the bilinearity of the tensor product. $\square$

**Theorem (Hilbert 90, Noether's form).** Let $L/K$ be a finite extension of fields and $G = \mathrm{Aut}_K(L)$. Each multiplicative $1$-cocycle $f \colon G \to L^\times$ is a coboundary. So $H^1(G, L^\times) = 1$.

*Proof.* The group $G$ is finite, because $L/K$ is finite. By Dedekind's theorem on the independence of characters, the distinct automorphisms $h \in G$ are linearly independent over $L$ as functions $L \to L$. The coefficients $f(h)$ are nonzero, so the function $z \mapsto \sum_{h} f(h)\, h(z)$ is not zero. Choose $z$ with $S = \sum_h f(h)\, h(z) \neq 0$. For $g \in G$,
$$g(S) = \sum_h g(f(h))\, gh(z).$$
The cocycle condition gives $g(f(h)) = f(gh) f(g)^{-1}$. So $g(S) = f(g)^{-1} \sum_h f(gh)\, gh(z) = f(g)^{-1} S$, because $h \mapsto gh$ is a bijection of $G$. Put $\beta = S^{-1}$. Then $g(\beta)/\beta = S/g(S) = f(g)$. $\square$

**Corollary (Hilbert 90, classical form).** Let $L/K$ be a finite Galois extension with cyclic Galois group generated by $\sigma$. If $x \in L$ has norm $N_{L/K}(x) = \prod_{g} g(x) = 1$, then $x = y / \sigma(y)$ for some $y \in L^\times$.

*Proof.* Let $n = [L : K]$. Define $f(\sigma^i) = x\, \sigma(x) \cdots \sigma^{i-1}(x)$ for $0 \leq i < n$. Because $N(x) = 1$, the same formula holds for all $i \geq 0$ with $\sigma^i$ read modulo $n$: $f(\sigma^n) = N(x) = 1 = f(1)$. Then $f(\sigma^{i+j}) = f(\sigma^i)\, \sigma^i(f(\sigma^j))$, which is the multiplicative cocycle condition. By the theorem, $f(g) = g(\beta)/\beta$. In particular $x = f(\sigma) = \sigma(\beta)/\beta$. Put $y = \beta^{-1}$: then $y/\sigma(y) = \sigma(\beta)/\beta = x$. $\square$

Mathlib proves the classical form differently: it uses the computation of $H^1$ of a cyclic group from Section 3, $H^1 \cong \ker N / \mathrm{im}(\sigma - 1)$, and the vanishing of $H^1$.

### Examples

**Example (A sign representation).** Let $G = \mathbb{Z}/2 = \{1, s\}$ act on $A = \mathbb{Z}$ by $s \cdot m = -m$. A crossed homomorphism has $f(1) = 0$, and $f(s)= a$ must satisfy $0 = f(s^2) = s f(s) + f(s) = -a + a$, which holds for all $a$. So $Z^1 \cong \mathbb{Z}$. A principal one has $f(s) = s m - m = -2m$. So $H^1(\mathbb{Z}/2, \mathbb{Z}_{\mathrm{sign}}) \cong \mathbb{Z}/2\mathbb{Z}$. For the trivial action, $H^1(\mathbb{Z}/2, \mathbb{Z}) = \mathrm{Hom}(\mathbb{Z}/2, \mathbb{Z}) = 0$.

**Example (The extension $\mathbb{Z}/4$).** Let $G = \mathbb{Z}/2$ act trivially on $A = \mathbb{Z}/2$. The extension $0 \to \mathbb{Z}/2 \xrightarrow{2} \mathbb{Z}/4 \to \mathbb{Z}/2 \to 0$ with the section $s(0) = 0$, $s(1) = 1$ has the cocycle $f(1, 1) = s(1) + s(1) - s(0) = 2$, the nonzero element of $A$, and $f = 0$ at the other three pairs. It is not a coboundary: a coboundary $dx$ with $dx(0, 0) = f(0,0) = 0$ has $x(0) = 0$, so $dx(1, 1) = 2x(1) - x(0) = 0$ in $\mathbb{Z}/2$. The split extension is $\mathbb{Z}/2 \times \mathbb{Z}/2$. In fact $H^2(\mathbb{Z}/2, \mathbb{Z}/2) \cong \mathbb{Z}/2$ (Section 3), so these are the only two classes.

**Example (Abelianization of $S_3$).** $H_1(S_3, \mathbb{Z}) \cong S_3^{\mathrm{ab}} \cong \mathbb{Z}/2$, the sign. For $A = \mathbb{Z}/3$ with trivial action, $H_1(S_3, \mathbb{Z}/3) \cong \mathbb{Z}/2 \otimes \mathbb{Z}/3 = 0$, and $H^1(S_3, \mathbb{Z}/3) = \mathrm{Hom}(S_3, \mathbb{Z}/3) = 0$.

**Example (Hilbert 90 for the Gaussian numbers).** Let $L = \mathbb{Q}(i)$, $K = \mathbb{Q}$, with $\sigma$ the complex conjugation. The element $x = (3 + 4i)/5$ has norm $x \bar x = (9 + 16)/25 = 1$. The corollary gives $y$ with $y/\bar y = x$. Take $y = 2 + i$: $y/\bar y = (2+i)/(2-i) = (2+i)^2/5 = (3 + 4i)/5$. In general, writing $y = a + bi$, the elements of norm $1$ are $((a^2 - b^2) + 2ab\, i)/(a^2 + b^2)$, which is the parametrization of the Pythagorean triples.

**Example (A cocycle for $\mathbb{C}/\mathbb{R}$).** For $G = \mathrm{Gal}(\mathbb{C}/\mathbb{R}) = \{1, \sigma\}$, a multiplicative cocycle $f$ has $f(1) = 1$, and $f(\sigma) = z$ with $1 = f(\sigma^2) = \sigma(z) z = |z|^2$. For $z = i$, the theorem gives $\beta$ with $\sigma(\beta)/\beta = i$; one solution is $\beta = 1 - i$, since $(1 + i)/(1 - i) = (1+i)^2/2 = i$.

### The library around it

::: mathlib
`groupCohomology.mem_cocycles₁_iff` · `Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree`

The file defines the low differentials `d₀₁`, `d₁₂`, `d₂₃` as maps between `A`, `G → A`, `G × G → A` and `G × G × G → A`, which is more convenient than `Fin n → G`. `cocycles₁ A` is the kernel of `d₁₂`, and `mem_cocycles₁_iff` states `f ∈ cocycles₁ A ↔ ∀ g h, f (g * h) = A.ρ g (f h) + f g`. `coboundaries₁ A` is the range of `d₀₁`, and `cocycles₂`, `coboundaries₂`, `mem_cocycles₂_iff` treat degree $2$. The predicates `IsCocycle₁`, `IsCocycle₂`, `IsCoboundary₁`, `IsCoboundary₂` state the same conditions for a function with values in any additive group with a `G`-action, and `IsMulCocycle₁`, `IsMulCoboundary₁` are the multiplicative forms. The normalization facts are `map_one_of_isCocycle₁`, `map_one_fst_of_isCocycle₂` and `map_one_snd_of_isCocycle₂`.

<?decl groupCohomology.mem_cocycles₁_iff?>
:::

::: mathlib
`groupCohomology.H1IsoOfIsTrivial` · `Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree`

`H0`, `H1`, `H2` are abbreviations for `groupCohomology A 0`, `1`, `2`. `H0Iso A : H0 A ≅ ↧A.ρ.invariants` is the first proposition, and `H0IsoOfIsTrivial` its trivial case. `H1π A : ↧(cocycles₁ A) ⟶ H1 A` is the quotient map, `H1π_eq_zero_iff` says that a class vanishes if and only if the cocycle is a coboundary, and `H1_induction_on` reduces a statement about `H1 A` to cocycles. `H1IsoOfIsTrivial A : H1 A ≅ ↧(Additive G →+ A)` is the theorem for a trivial action, with `Additive G` because Mathlib's additive homomorphisms need an additive source. `H2π` and `H2π_eq_zero_iff` are the degree $2$ versions. The theorem on extensions is not in this file; the index of this edition has no declaration for the classification of extensions by $H^2$.

<?decl groupCohomology.H1IsoOfIsTrivial?>
:::

::: mathlib
`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units` · `Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90`

This is Noether's theorem for a finite extension `L/K`, stated with the predicates `IsMulCocycle₁` and `IsMulCoboundary₁` on functions `Gal(L/K) → Lˣ`. The proof follows the text: `Hilbert90.aux f` is the function $z \mapsto \sum f(h) h(z)$, which is nonzero by Dedekind independence, and $\beta$ is the inverse of one value. The instance `H1ofAutOnUnitsUnique` restates it as `Unique (H1 (Rep.ofAlgebraAutOnUnits K L))`, where the representation is the action on $L^\times$ as an additive group. `exists_div_of_norm_eq_one` is the classical form for a cyclic Galois extension, and `exists_mul_galRestrict_of_norm_eq_one` is a version for rings of integers.

<?decl groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units?>
:::

::: mathlib
`groupHomology.H1AddEquivOfIsTrivial` · `Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree`

For a trivial representation, `H1AddEquivOfIsTrivial A : H1 A ≃+ (Additive (Abelianization G)) ⊗[ℤ] A` sends the class of `single g a` to $\bar g \otimes a$, as in the proof. `H1ToTensorOfIsTrivial` and `mkH1OfIsTrivial` are the two directions. In degree $0$, `H0Iso A : H0 A ≅ (coinvariantsFunctor k G).obj A`, and `range_d₁₀_eq_coinvariantsKer` says that the image of `d₁₀` is the submodule $I_G A$. The differentials `d₁₀` and `d₂₁` use $\rho(g^{-1})$, as in Section 1.

<?decl groupHomology.H1AddEquivOfIsTrivial?>
:::

Common errors of a learner: The first error is to write the cocycle condition as $f(gh) = f(g) + g f(h)$ and to expect Mathlib to match it syntactically; Mathlib writes `A.ρ g (f h) + f g`, so a rewrite may need `add_comm`. The second error is to treat $L^\times$ as a representation directly; Mathlib needs `Rep.ofAlgebraAutOnUnits K L`, with `Additive Lˣ` as the module, which is why the multiplicative predicates exist. The third error is to forget that Noether's theorem in Mathlib takes $G = \mathrm{Aut}_K(L)$ and needs no Galois hypothesis, while the classical form needs `IsGalois K L` and a cyclic Galois group. The fourth error is to confuse $H^1(G, A) = \mathrm{Hom}(G, A)$ for a trivial action with $H_1(G, A) = G^{\mathrm{ab}} \otimes A$; for $G = \mathbb{Z}/2$ and $A = \mathbb{Z}$ the first is $0$ and the second is $\mathbb{Z}/2$.

### Exercises

1. (A) Compute $H^0$ and $H_0$ of $\mathbb{Z}/3$ acting on $\mathbb{Z}^3$ by cyclic permutation of coordinates. Hint: $H^0 = \mathbb{Z}(1,1,1)$ and $H_0 = \mathbb{Z}$ via the sum of the coordinates.
2. (A) Show that $H^1(\mathbb{Z}, A) \cong A / (t - 1)A$, where $t$ is the generator of $\mathbb{Z}$. Hint: a crossed homomorphism on $\mathbb{Z}$ is determined by $f(t)$, and each value is allowed.
3. (B) Show that the semidirect products $A \rtimes G$ have their complements to $A$ in bijection with $Z^1(G, A)$, and their conjugacy classes of complements (under conjugation by $A$) in bijection with $H^1(G, A)$. Hint: a complement is the image of a section $g \mapsto (f(g), g)$.
4. (B) Find the cocycle of the extension $1 \to \mathbb{Z}/2 \to Q_8 \to \mathbb{Z}/2 \times \mathbb{Z}/2 \to 1$ for the section $1, i, j, k$, and show that it is not a coboundary. Hint: $f(i, j) = 0$ but $f(j, i) \neq 0$, while a coboundary for a trivial action of an abelian group is symmetric in its two arguments.
5. (B) Prove the additive form of Hilbert 90 for a finite Galois extension: $H^1(\mathrm{Gal}(L/K), L) = 0$. Hint: by the normal basis theorem $L \cong K[G]$, or choose $z$ with trace $1$ and put $m = -\sum_h f(h)\, h(z)$.
6. (C) Use the corollary to find all rational points on the circle $x^2 + y^2 = 1$. Hint: the example of the Gaussian numbers.
7. (C) Let $G$ be a finite group of order $n$. Show that $n \cdot H^1(G, A) = 0$. Hint: for a cocycle $f$, sum the cocycle condition over $h$ and put $m = \sum_h f(h)$.

### Notes and history

Hilbert stated Theorem 90 in his report on algebraic number fields of 1897, for cyclic extensions and in the form of the corollary. Noether generalized it to the vanishing of $H^1$ for any finite Galois extension, before group cohomology had a name. Crossed homomorphisms and factor sets, the $2$-cocycles of extensions, were used by Schreier and others to classify group extensions. Eilenberg and MacLane placed these computations inside the cohomology of groups in the 1940s.

The Mathlib files are by these authors, read from their headers: `GroupCohomology.LowDegree` by Amelia Livingston and Joël Riou; `GroupCohomology.Hilbert90` by Riccardo Brasca and Amelia Livingston; `GroupHomology.LowDegree` by Amelia Livingston.

### Reference

<?reference?>
