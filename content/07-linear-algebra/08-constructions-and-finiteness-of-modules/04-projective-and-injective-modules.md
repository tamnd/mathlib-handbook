---
title: Projective, injective and stably free modules
kind: api
modules:
  - Mathlib.Algebra.Module.Projective
  - Mathlib.Algebra.Module.Injective
  - Mathlib.Algebra.Module.CharacterModule
  - Mathlib.Algebra.Module.StablyFree.Basic
  - Mathlib.Algebra.Module.StablyFree.FreeOfInvertible
  - Mathlib.Algebra.Module.SnakeLemma
explains:
  E2: [Module.Projective, Module.projective_lifting_property, Module.Projective.iff_split, Module.Injective, Module.Baer.injective, CharacterModule, CharacterModule.homEquiv, Module.IsStablyFree, Module.free_of_isStablyFree_of_invertible, SnakeLemma.δ]
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

## Projective, injective and stably free modules

### Overview

Free modules are the simplest modules, but many constructions give modules that are close to free and not free. A projective module is a direct summand of a free module. Equivalently, each map from it lifts along each surjection. An injective module is the dual notion: each map into it extends along each injective map. A stably free module becomes free after a sum with a finite free module. This section covers the three classes `Module.Projective`, `Module.Injective` and `Module.IsStablyFree`, Baer's criterion for injectivity, the character module $\operatorname{Hom}(M, \mathbb{Q}/\mathbb{Z})$, and the snake lemma for modules, which gives the connecting map in the long exact sequences that these classes control.

### The library around it

#### Projective modules

The class `Module.Projective R P` is defined by a splitting. The map $\varepsilon : R^{(P)} \to P$ sends the basis vector $e_p$ to $p$, and $P$ is projective if $\varepsilon$ has a linear right inverse $s$ (`Module.projective_def`). The definition works over a semiring. The usual definition is the lifting property.

**Theorem.** Let $P$ be projective. For each surjective linear map $f : M \to N$ and each linear map $g : P \to N$ there is a linear map $h : P \to M$ with $f \circ h = g$.

*Proof.* For each $p \in P$ choose $m_p \in M$ with $f(m_p) = g(p)$. The map $R^{(P)} \to M$ with $e_p \mapsto m_p$ composed with $s$ is the map $h$. Then $f(h(x)) = \sum_p c_p f(m_p) = \sum_p c_p g(p) = g(\varepsilon(s(x))) = g(x)$, where $s(x) = \sum_p c_p e_p$. $\square$

This is `Module.projective_lifting_property`. The converse is `Module.Projective.of_lifting_property`: a module with the lifting property for each surjection is projective. A special case is a splitting: a surjection onto a projective module has a right inverse (`LinearMap.exists_rightInverse_of_surjective`).

**Theorem.** A module is projective if and only if it is a direct summand of a free module.

*Proof.* If $P$ is projective, then $s$ embeds $P$ into the free module $R^{(P)}$ with the retraction $\varepsilon$. Conversely, let $i : P \to F$ and $r : F \to P$ with $r \circ i = \mathrm{id}$ and $F$ free. A free module is projective, since a basis gives the lifts. A lift of $g \circ r$ through $f$, composed with $i$, is a lift of $g$. $\square$

This is `Module.Projective.iff_split`, with `Module.Projective.of_split` for the converse direction. Free modules are projective by the instance `Module.Projective.of_free` and by `Module.Projective.of_basis`. The class is kept by products (`Module.instProjectiveProd`), by direct sums (`Module.Projective.directSum`, and `Module.Projective.directSum_iff` for the converse), by finitely supported functions, by linear equivalences (`Module.Projective.of_equiv`), and along a tower $R \to S$ (`Module.Projective.trans`). Over a principal ideal domain, a finitely generated projective module is free, by the structure theorem of Chapter 7.

#### Injective modules

The class `Module.Injective R Q` says that for each injective linear map $f : X \to Y$ and each $g : X \to Q$ there is $h : Y \to Q$ with $h \circ f = g$. In the definition, $X$ and $Y$ are in the same universe as $Q$; the form for all universes is `Module.Injective.extension_property`. The class needs a ring.

To check injectivity, it is enough to test the inclusions of ideals into $R$. The predicate `Module.Baer R Q` says that each linear map $I \to Q$ from an ideal $I$ extends to $R$.

**Theorem.** (Baer's criterion) If $Q$ satisfies `Module.Baer R Q`, then $Q$ is injective.

*Proof.* Let $f : X \to Y$ be injective and $g : X \to Q$. Consider the partial extensions: pairs of a submodule $D \supseteq f(X)$ of $Y$ and a map $D \to Q$ that extends $g \circ f^{-1}$. They are ordered by extension, and a chain has an upper bound on the union. By Zorn's lemma there is a maximal extension $(D, h)$. Suppose $y \notin D$. The set $I = \{r \in R : r y \in D\}$ is an ideal, and $r \mapsto h(r y)$ is a linear map $I \to Q$. By Baer's condition it extends to $\varphi : R \to Q$. Then $d + r y \mapsto h(d) + \varphi(r)$ is well defined on $D + R y$ and extends $h$, which is a contradiction. So $D = Y$. $\square$

This is `Module.Baer.injective`, and `Module.Baer.iff_injective` gives the converse. The maximal extension is `Module.Baer.extensionOfMax`, and the partial extensions are the structure `Module.Baer.ExtensionOf`. Over $\mathbb{Z}$, a divisible group satisfies Baer's criterion (`Module.Baer.of_divisible`), so $\mathbb{Q}$ and $\mathbb{Q}/\mathbb{Z}$ are injective $\mathbb{Z}$-modules. Products of injective modules are injective (`Module.Injective.pi`).

#### Character modules

The character module of an abelian group $A$ is `CharacterModule A`, the group of additive maps $A \to \mathbb{Q}/\mathbb{Z}$, where $\mathbb{Q}/\mathbb{Z}$ is the circle `AddCircle (1 : ℚ)`. If $A$ is an $R$-module, the character module is an $R$-module with $(r c)(a) = c(r a)$. A linear map $f : A \to B$ gives the dual map `CharacterModule.dual f` from the characters of $B$ to the characters of $A$.

Since $\mathbb{Q}/\mathbb{Z}$ is injective, the characters separate the points: for $a \ne 0$ there is a character $c$ with $c(a) \ne 0$ (`CharacterModule.exists_character_apply_ne_zero_of_ne_zero`). From this, $f$ is injective if and only if its dual is surjective (`CharacterModule.dual_surjective_iff_injective`), and $f$ is surjective if and only if its dual is injective (`CharacterModule.dual_injective_iff_surjective`).

**Theorem.** For $R$-modules $A$ and $B$, the linear maps $A \to B^{*}$ are in bijection with the characters of $A \otimes_R B$, where $B^{*}$ is the character module.

*Proof.* A linear map $\varphi : A \to B^{*}$ gives the map $A \times B \to \mathbb{Q}/\mathbb{Z}$, $(a, b) \mapsto \varphi(a)(b)$. This map is $R$-bilinear, so it factors through $A \otimes_R B$. Conversely, a character $c$ of $A \otimes_R B$ gives $a \mapsto (b \mapsto c(a \otimes b))$. The two constructions are inverse. $\square$

This is `CharacterModule.homEquiv`, with `CharacterModule.curry` and `CharacterModule.uncurry`. It turns a question about the tensor product into a question about linear maps: `LinearMap.rTensor B f` is injective if and only if the composition with $f$ on maps into $B^{*}$ is surjective (`rTensor_injective_iff_lcomp_surjective`). This is the tool that relates flat modules to injective character modules.

#### Stably free modules

The class `Module.IsStablyFree R M` says that $M \times N$ is free for some finite free module $N$ (`Module.IsStablyFree.exist_free_prod`). A free module is stably free, and a stably free module is projective, by the instances `Module.instIsStablyFreeOfFree` and `Module.instProjectiveOfIsStablyFree`. A stably free module need not be free. The tangent bundle of the 2-sphere gives the standard example: over $\mathbb{R}[x, y, z]/(x^2 + y^2 + z^2 - 1)$, the kernel of $(a, b, c) \mapsto a x + b y + c z$ is stably free and not free.

**Theorem.** Over a commutative ring, an invertible stably free module is free.

*Proof.* Let $M$ be invertible, so that $M$ is finite projective of rank $1$ at each prime, and let $M \oplus R^n \simeq R^m$. A comparison of the ranks at a prime gives $m = n + 1$. Take the exterior power $\Lambda^{n + 1}$ of both sides. Since $\Lambda^i M = 0$ for $i \ge 2$, the left side is $M \otimes \Lambda^n R^n \simeq M$, and the right side is $\Lambda^{n + 1} R^{n + 1} \simeq R$. So $M \simeq R$. $\square$

This is `Module.free_of_isStablyFree_of_invertible`. The class is kept by linear equivalences (`Module.IsStablyFree.equiv_iff`) and `Module.IsStablyFree.of_free_prod` is the constructor from a free product $M \times N$.

#### The snake lemma for modules

The long exact sequences of homological algebra start from the snake lemma. Take a commutative diagram with exact rows $M_1 \to M_2 \to M_3$ and $N_1 \to N_2 \to N_3$, vertical maps $i_k : M_k \to N_k$, the kernel $K_3$ of $i_3$, and the cokernel $C_1$ of $i_1$. Let $M_2 \to M_3$ be surjective and $N_1 \to N_2$ be injective. Then there is a connecting map $\delta : K_3 \to C_1$: lift $x \in K_3$ to $y \in M_2$, map it to $i_2(y) \in N_2$, which lies in the image of $N_1$, and take the class of the preimage in $C_1$.

The map is `SnakeLemma.δ`, and `SnakeLemma.δ_eq` is the formula above. The exactness of $K_2 \to K_3 \to C_1$ is `SnakeLemma.exact_δ_right`, and the exactness of $K_3 \to C_1 \to C_2$ is `SnakeLemma.exact_δ_left`. The general snake lemma holds in each abelian category, but the form for modules has better definitional equalities and no universe conditions. The variant `SnakeLemma.δ'` takes the surjectivity and the injectivity as hypotheses in place of the set maps that split them.

#### Common errors

1. Expecting `Module.Injective` over a semiring. The class and Baer's criterion need a ring. `Module.Projective` works over a semiring.
2. Applying `Module.Injective.out` to modules in a different universe. The field quantifies only over the universe of $Q$; use `Module.Injective.extension_property` for the general case.
3. Expecting a stably free module to be free. This needs extra conditions, such as `Module.free_of_isStablyFree_of_invertible` in rank $1$ or the structure theorem over a principal ideal domain.

### Exercises

1. (A) Show that $\mathbb{Z}/2$ is not a projective $\mathbb{Z}$-module, with the surjection $\mathbb{Z} \to \mathbb{Z}/2$.
2. (A) Show that $\mathbb{Z}$ is not an injective $\mathbb{Z}$-module, with the map $2 : \mathbb{Z} \to \mathbb{Z}$.
3. (B) Let $R = \mathbb{Z}/6$. Show that $\mathbb{Z}/2$ is a projective $R$-module that is not free.
4. (B) Show that each $R$-module embeds in an injective $R$-module, given that $\mathbb{Q}/\mathbb{Z}$ is an injective $\mathbb{Z}$-module.
5. (B) Show that a direct summand of a stably free module need not be stably free, with the example of Exercise 3.
6. (C) Use the snake lemma to show that in a commutative diagram of short exact sequences, if the two outer vertical maps are isomorphisms, then the middle map is an isomorphism.

### Reference

<?reference?>
