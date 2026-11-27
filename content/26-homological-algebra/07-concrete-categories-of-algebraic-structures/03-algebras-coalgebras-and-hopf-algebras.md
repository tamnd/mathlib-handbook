---
title: Algebras, coalgebras and Hopf algebras
kind: theory
modules:
  - Mathlib.Algebra.Category.AlgCat.Basic
  - Mathlib.Algebra.Category.CommAlgCat.Basic
  - Mathlib.Algebra.Category.CoalgCat.Basic
  - Mathlib.Algebra.Category.CoalgCat.ComonEquivalence
  - Mathlib.Algebra.Category.BialgCat.Basic
  - Mathlib.Algebra.Category.HopfAlgCat.Basic
explains:
  E3: [AlgCat.adj, AlgCat.intEquivalence, commAlgCatEquivUnder, instHasColimitsCommAlgCat, instHasLimitsCommAlgCat, CoalgCat.comonEquivalence, CoalgCat.instMonoidalCategoryAux]
  E2: [AlgCat, AlgCat.of, AlgCat.ofHom, AlgCat.free, AlgCat.hasForgetToRing, AlgCat.hasForgetToModule, AlgEquiv.toAlgebraIso, AlgCat.restrictScalars, CommAlgCat, CommAlgCat.of, CommAlgCat.ofHom, CommAlgCat.isoMk, CommAlgCat.homEquivCommRingCat, CommAlgCat.isoEquivAlgEquiv, CoalgCat, CoalgCat.of, CoalgCat.ofHom, CoalgCat.Hom.toCoalgHom, CoalgCat.hasForgetToModule, CoalgEquiv.toCoalgIso, CoalgCat.toComon, CoalgCat.ofComon, BialgCat, BialgCat.of, BialgCat.ofHom, BialgCat.hasForgetToAlgebra, BialgCat.hasForgetToCoalgebra, HopfAlgCat, HopfAlgCat.of, HopfAlgCat.ofHom, HopfAlgCat.hasForgetToBialgebra]
  E1: auto
families: []
requires: [V24.C04, V24.C05, V24.C07, V08.C02, V08.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Algebras, coalgebras and Hopf algebras

### Overview

Throughout this section $R$ is a commutative ring and $\otimes$ means $\otimes_R$. An $R$-algebra is a monoid in the monoidal category $(\mathrm{Mod}_R, \otimes, R)$ of Section 2. Reversing the arrows gives a comonoid, which is a coalgebra. An object that is both, in a compatible way, is a bialgebra, and a bialgebra with an antipode is a Hopf algebra. The group algebra $k[G]$ is a Hopf algebra, and this structure is the reason why the tensor product of two representations of $G$ and the dual of a representation are again representations. Chapter 8 uses this fact without comment.

This section defines the five categories of Mathlib: algebras, commutative algebras, coalgebras, bialgebras and Hopf algebras. It proves the free algebra adjunction, the equivalence between commutative $R$-algebras and commutative rings under $R$ (from which limits and colimits follow), the equivalence between coalgebras and comonoids in $\mathrm{Mod}_R$, and the fact that a morphism of bialgebras between Hopf algebras preserves the antipodes. In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`.

### Definitions

**Definition (Algebra).** An $R$-algebra is a ring $A$ with a ring homomorphism $\eta \colon R \to A$ whose image is central. Equivalently, it is an $R$-module $A$ with $R$-linear maps $\mu \colon A \otimes A \to A$ and $\eta \colon R \to A$ that satisfy associativity $\mu \circ (\mu \otimes \mathrm{id}) = \mu \circ (\mathrm{id} \otimes \mu)$ and the unit laws $\mu \circ (\eta \otimes \mathrm{id}) = \mathrm{id} = \mu \circ (\mathrm{id} \otimes \eta)$, up to the unitors. A morphism is a ring homomorphism $f$ with $f \circ \eta_A = \eta_B$. The category is $\mathrm{Alg}_R$, and $\mathrm{CAlg}_R$ is its full subcategory of commutative algebras.

**Definition (Coalgebra).** An $R$-coalgebra is an $R$-module $C$ with $R$-linear maps $\Delta \colon C \to C \otimes C$ (comultiplication) and $\varepsilon \colon C \to R$ (counit) such that
$$(\Delta \otimes \mathrm{id}) \circ \Delta = (\mathrm{id} \otimes \Delta) \circ \Delta, \qquad (\varepsilon \otimes \mathrm{id}) \circ \Delta = \mathrm{id} = (\mathrm{id} \otimes \varepsilon) \circ \Delta,$$
up to the associator and the unitors. A morphism of coalgebras is a linear map $f \colon C \to D$ with $(f \otimes f) \circ \Delta_C = \Delta_D \circ f$ and $\varepsilon_D \circ f = \varepsilon_C$.

**Definition (Comonoid).** In a monoidal category $(\mathcal{C}, \otimes, I)$, a comonoid is an object $C$ with maps $\Delta \colon C \to C \otimes C$ and $\varepsilon \colon C \to I$ that satisfy coassociativity and the counit laws, written with the associator and unitors of $\mathcal{C}$. A morphism of comonoids commutes with $\Delta$ and $\varepsilon$. The category is $\mathrm{Comon}(\mathcal{C})$ (Volume 24, Chapter 7, has the dual notion of monoid).

**Definition (Bialgebra and Hopf algebra).** A bialgebra is an $R$-algebra $B$ with a coalgebra structure such that $\Delta$ and $\varepsilon$ are algebra homomorphisms; here $B \otimes B$ carries the product $(a \otimes b)(a' \otimes b') = aa' \otimes bb'$. A morphism of bialgebras is a map that is both an algebra and a coalgebra morphism. A Hopf algebra is a bialgebra $H$ with a linear map $S \colon H \to H$, the antipode, such that
$$\mu \circ (S \otimes \mathrm{id}) \circ \Delta = \eta \circ \varepsilon = \mu \circ (\mathrm{id} \otimes S) \circ \Delta.$$
A morphism of Hopf algebras is a morphism of bialgebras.

**Definition (Convolution).** For a coalgebra $C$ and an algebra $A$, the convolution of linear maps $f, g \colon C \to A$ is $f * g = \mu \circ (f \otimes g) \circ \Delta$. In Sweedler's notation $\Delta(c) = \sum c_{(1)} \otimes c_{(2)}$, this reads $(f * g)(c) = \sum f(c_{(1)}) g(c_{(2)})$.

### Theorems and proofs

**Proposition (Free algebra).** The free algebra functor $X \mapsto R\langle X \rangle$, the algebra of noncommutative polynomials in the variables $X$, is left adjoint to the forgetful functor $\mathrm{Alg}_R \to \mathbf{Set}$. The polynomial algebra $R[X]$ is left adjoint to the forgetful functor $\mathrm{CAlg}_R \to \mathbf{Set}$.

*Proof.* The algebra $R\langle X \rangle$ has the $R$-basis of words $x_1 x_2 \cdots x_n$, $n \geq 0$, with concatenation as product. A map of sets $\phi \colon X \to A$ extends to the linear map that sends $x_1 \cdots x_n$ to $\phi(x_1) \cdots \phi(x_n)$. It is multiplicative on words, hence on all elements, and it sends the empty word to $1$. It is the unique such extension, because an algebra map is determined by its values on generators. Restriction to $X$ gives the inverse bijection, and both directions are natural. For $R[X]$ the same proof works with monomials, and the extension is multiplicative because $A$ is commutative. $\square$

**Theorem (Commutative algebras are rings under $R$).** The category $\mathrm{CAlg}_R$ is equivalent to the category $R/\mathbf{CRing}$ of commutative rings $A$ with a ring map $R \to A$, where a morphism is a ring map that commutes with the maps from $R$. So $\mathrm{CAlg}_R$ has all small limits and colimits. The coproduct of $A$ and $B$ is $A \otimes B$.

*Proof.* A commutative $R$-algebra gives its structure map $\eta \colon R \to A$, and an algebra map is a ring map with $f \circ \eta_A = \eta_B$. Conversely, a ring map $\eta \colon R \to A$ to a commutative ring gives the algebra structure $r \cdot a = \eta(r) a$; the centrality condition is automatic. The two functors are inverse to each other up to the identity on the underlying rings, so they form an equivalence.

The category $\mathbf{CRing}$ has all limits (Section 1) and all colimits; the second fact is in Mathlib. A coslice category $R/\mathcal{C}$ of a complete and cocomplete category is complete and cocomplete: a colimit of a diagram under $R$ is the colimit in $\mathcal{C}$ of the diagram with the extra object $R$, and a limit of a diagram under $R$ is the limit in $\mathcal{C}$, with the map from $R$ given by the universal property. Equivalent categories have the same limits and colimits. For the coproduct: given algebra maps $f \colon A \to C$ and $g \colon B \to C$, the map $A \times B \to C$, $(a, b) \mapsto f(a) g(b)$, is $R$-bilinear, so it gives a linear map $A \otimes B \to C$. It is an algebra map because $C$ is commutative: $f(aa') g(bb') = f(a) g(b) f(a') g(b')$. It is the unique map that restricts to $f$ on $a \otimes 1$ and to $g$ on $1 \otimes b$, because these elements generate $A \otimes B$ as an algebra. $\square$

**Theorem (Coalgebras are comonoids).** The category of $R$-coalgebras is equivalent to $\mathrm{Comon}(\mathrm{Mod}_R)$.

*Proof.* The data of a coalgebra on $C$ are exactly the data of a comonoid on the object $C$ of $\mathrm{Mod}_R$: a map $C \to C \otimes C$ and a map $C \to R$, where $R$ is the unit object. The axioms of a coalgebra are the axioms of a comonoid, once one writes the associator $(C \otimes C) \otimes C \cong C \otimes (C \otimes C)$ and the unitors $R \otimes C \cong C$ explicitly. The morphisms are the same in the two categories: linear maps that commute with $\Delta$ and $\varepsilon$. So the functor $C \mapsto (C, \Delta, \varepsilon)$ and its inverse are identities on morphisms and on underlying modules, and they give an equivalence whose unit and counit are identities. $\square$

The equivalence gives a monoidal structure on coalgebras. The category $\mathrm{Mod}_R$ is symmetric monoidal, and the comonoids of a braided monoidal category form a monoidal category. For coalgebras $C$ and $D$, the tensor product $C \otimes D$ has
$$\Delta(c \otimes d) = \sum (c_{(1)} \otimes d_{(1)}) \otimes (c_{(2)} \otimes d_{(2)}), \qquad \varepsilon(c \otimes d) = \varepsilon(c)\varepsilon(d).$$
The middle factors are swapped by the braiding. With this structure, a bialgebra is a monoid in the monoidal category of coalgebras.

**Proposition (Morphisms preserve antipodes).** Let $f \colon H \to K$ be a morphism of bialgebras between Hopf algebras with antipodes $S_H$ and $S_K$. Then $f \circ S_H = S_K \circ f$.

*Proof.* Work in the set $\mathrm{Hom}_R(H, K)$ with the convolution product $*$, where $H$ is the coalgebra and $K$ is the algebra. Convolution is associative by coassociativity of $\Delta_H$ and associativity of $\mu_K$, and $e = \eta_K \circ \varepsilon_H$ is a two-sided unit by the counit laws. Compute three convolutions.

First, $(f \circ S_H) * f = \mu_K \circ (f \otimes f) \circ (S_H \otimes \mathrm{id}) \circ \Delta_H = f \circ \mu_H \circ (S_H \otimes \mathrm{id}) \circ \Delta_H$, because $f$ is an algebra map. By the antipode axiom this is $f \circ \eta_H \circ \varepsilon_H = \eta_K \circ \varepsilon_H = e$.

Second, $f * (S_K \circ f) = \mu_K \circ (\mathrm{id} \otimes S_K) \circ (f \otimes f) \circ \Delta_H = \mu_K \circ (\mathrm{id} \otimes S_K) \circ \Delta_K \circ f$, because $f$ is a coalgebra map. By the antipode axiom of $K$ this is $\eta_K \circ \varepsilon_K \circ f = \eta_K \circ \varepsilon_H = e$.

Third, by associativity,
$$f \circ S_H = (f \circ S_H) * e = (f \circ S_H) * (f * (S_K \circ f)) = ((f \circ S_H) * f) * (S_K \circ f) = e * (S_K \circ f) = S_K \circ f. \qquad \square$$

This proposition explains why Mathlib defines the morphisms of `HopfAlgCat` as bialgebra morphisms with no condition on the antipode. The same argument with $f = \mathrm{id}$ shows that the antipode of a bialgebra is unique if it exists.

### Examples

**Example (The group algebra).** Let $G$ be a group and $k$ a commutative ring. The group algebra $k[G]$ has basis $G$ and product $g \cdot h = gh$. It is a Hopf algebra with $\Delta(g) = g \otimes g$, $\varepsilon(g) = 1$ and $S(g) = g^{-1}$. The antipode axiom holds on the basis: $\mu(S \otimes \mathrm{id})\Delta(g) = g^{-1} g = 1 = \eta(\varepsilon(g))$. For two representations $V$, $W$ of $G$, the map $\Delta$ makes $V \otimes W$ a representation with $g(v \otimes w) = gv \otimes gw$, and $S$ makes the dual $V^*$ a representation with $(g\phi)(v) = \phi(g^{-1} v)$. The counit gives the trivial representation $k$, which is the module that Chapter 8 resolves.

**Example (The polynomial Hopf algebra).** The algebra $k[x]$ is a Hopf algebra with $\Delta(x) = x \otimes 1 + 1 \otimes x$, $\varepsilon(x) = 0$ and $S(x) = -x$. Because $\Delta$ is an algebra map, $\Delta(x^2) = (x \otimes 1 + 1 \otimes x)^2 = x^2 \otimes 1 + 2\, x \otimes x + 1 \otimes x^2$, and in general $\Delta(x^n) = \sum_{i=0}^{n} \binom{n}{i} x^i \otimes x^{n-i}$. The antipode axiom on $x$ reads $S(x) \cdot 1 + S(1) \cdot x = -x + x = 0 = \varepsilon(x)$. The algebra maps $k[x] \to A$ are the elements of $A$, and $\Delta$ encodes the addition: this is the additive group as a group scheme.

**Example (A coalgebra that is not an algebra).** Let $C = k^n$ with basis $e_1, \dots, e_n$, and set $\Delta(e_i) = e_i \otimes e_i$ and $\varepsilon(e_i) = 1$. This is the coalgebra $k[X]$ of the set $X = \{1, \dots, n\}$. Its dual $C^* = \mathrm{Hom}(C, k)$ with the convolution product is the algebra $k^n$ of functions on $X$ with pointwise product, because $(\phi * \psi)(e_i) = \phi(e_i) \psi(e_i)$.

**Example (Free algebras and matrices).** By the adjunction, an algebra map $\mathbb{Q}\langle x, y \rangle \to M_2(\mathbb{Q})$ is a pair of matrices. The pair $x \mapsto \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$, $y \mapsto \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$ sends $xy - yx$ to $\begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix} \neq 0$. So this map does not factor through $\mathbb{Q}[x, y]$, which is the image of $R\langle X \rangle$ under the left adjoint of the inclusion $\mathrm{CAlg}_R \to \mathrm{Alg}_R$.

**Example (Coproducts of commutative algebras).** In $\mathrm{CAlg}_{\mathbb{Q}}$, the coproduct of $\mathbb{Q}[x]$ and $\mathbb{Q}[y]$ is $\mathbb{Q}[x] \otimes \mathbb{Q}[y] \cong \mathbb{Q}[x, y]$. The coproduct of $\mathbb{Q}(i) = \mathbb{Q}[x]/(x^2 + 1)$ with itself is $\mathbb{Q}(i) \otimes \mathbb{Q}(i) \cong \mathbb{Q}(i)[x]/(x^2 + 1) \cong \mathbb{Q}(i) \times \mathbb{Q}(i)$, because $x^2 + 1 = (x - i)(x + i)$ over $\mathbb{Q}(i)$. So a coproduct of fields need not be a field.

### The library around it

::: mathlib
`AlgCat.adj` · `Mathlib.Algebra.Category.AlgCat.Basic`

`AlgCat R` is a structure with a carrier, a `Ring` instance and an `Algebra R` instance; `AlgCat.of R A` and `AlgCat.ofHom f` follow the pattern of Section 1, and `AlgEquiv.toAlgebraIso` turns an algebra equivalence into an isomorphism. `AlgCat.free R` sends a type to `FreeAlgebra R S`, and `AlgCat.adj R : AlgCat.free R ⊣ forget (AlgCat R)` is the proposition above. The instances `AlgCat.hasForgetToRing` and `AlgCat.hasForgetToModule` give the forgetful functors. `AlgCat.intEquivalence : AlgCat ℤ ≌ RingCat` identifies $\mathbb{Z}$-algebras with rings. The monoidal structure `AlgCat.instMonoidalCategory` is in `Mathlib.Algebra.Category.AlgCat.Monoidal`, and the equivalence of algebras with monoids, `ModuleCat.monModuleEquivalenceAlgebra`, is in `Mathlib.CategoryTheory.Monoidal.Internal.Module`.

<?decl AlgCat.adj?>
:::

::: mathlib
`commAlgCatEquivUnder` · `Mathlib.Algebra.Category.CommAlgCat.Basic`

`commAlgCatEquivUnder R : CommAlgCat R ≌ Under R` for `R : CommRingCat` is the theorem above. The file deduces the instances `instHasColimitsCommAlgCat` and `instHasLimitsCommAlgCat` from it by `Adjunction.has_colimits_of_equivalence`, exactly as in the proof. `CommAlgCat.homEquivCommRingCat` describes a morphism as a ring map that commutes with the algebra maps, and `CommAlgCat.isoEquivAlgEquiv` identifies isomorphisms with algebra equivalences.

<?decl commAlgCatEquivUnder?>
:::

::: mathlib
`CoalgCat.comonEquivalence` · `Mathlib.Algebra.Category.CoalgCat.ComonEquivalence`

`CoalgCat.comonEquivalence : CoalgCat R ≌ Comon (ModuleCat R)`, built from `CoalgCat.toComon` and `CoalgCat.ofComon`; its unit and counit are identities, as in the proof. The file then defines `CoalgCat.instMonoidalCategoryAux`, the monoidal structure transported from comonoids, and uses it to prove that the comultiplication of a tensor product of coalgebras satisfies the axioms. The instance that users see, `CoalgCat.instMonoidalCategory`, is in `Mathlib.Algebra.Category.CoalgCat.Monoidal`; it has better definitional equalities. `BialgCat.instMonoidalCategory` is in `Mathlib.Algebra.Category.BialgCat.Monoidal`.

<?decl CoalgCat.comonEquivalence?>
:::

::: mathlib
`HopfAlgCat` · `Mathlib.Algebra.Category.HopfAlgCat.Basic`

`CoalgCat R` extends `ModuleCat R` with a `Coalgebra` instance, and its morphisms wrap coalgebra maps `V →ₗc[R] W` (`CoalgCat.Hom.toCoalgHom`). `BialgCat R` and `HopfAlgCat R` have a carrier with a `Ring` instance and a `Bialgebra` or `HopfAlgebra` instance. In both, a morphism wraps a bialgebra map `V →ₐc[R] W`, so a Hopf algebra morphism carries no antipode condition, which the proposition above justifies. `BialgCat.hasForgetToAlgebra`, `BialgCat.hasForgetToCoalgebra` and `HopfAlgCat.hasForgetToBialgebra` give the forgetful functors.

<?decl HopfAlgCat?>
:::

Common errors of a learner: The first error is to forget that $\otimes$ in the definition of a coalgebra is the tensor product over $R$, so that a comultiplication is not a map $C \to C \times C$. The second error is to write the tensor product of coalgebras without the braiding: the formula for $\Delta(c \otimes d)$ needs the swap of the middle factors. The third error is to look for an antipode condition in the morphisms of `HopfAlgCat`. The fourth error is to apply `commAlgCatEquivUnder` to a ring `R` of type `Type`: it takes `R : CommRingCat`. The fifth error is to expect that the forgetful functor from `CommAlgCat R` to `Type` preserves coproducts; the coproduct is the tensor product.

### Exercises

1. (A) Check that $\varepsilon \colon k[G] \to k$, $\sum a_g g \mapsto \sum a_g$, is an algebra map and satisfies the counit law. Hint: work on the basis.
2. (A) Compute $\Delta(x^3)$ in the polynomial Hopf algebra $k[x]$ and check that $S(x^2) = x^2$. Hint: $S$ is an algebra anti-homomorphism, and $k[x]$ is commutative.
3. (B) Show that $\mathbb{Q}(\sqrt 2) \otimes \mathbb{Q}(\sqrt 2) \cong \mathbb{Q}(\sqrt 2) \times \mathbb{Q}(\sqrt 2)$ and $\mathbb{F}_p(t^{1/p}) \otimes_{\mathbb{F}_p(t)} \mathbb{F}_p(t^{1/p})$ is not reduced. Hint: factor $x^2 - 2$ and $x^p - t = (x - t^{1/p})^p$.
4. (B) Prove that the antipode of a Hopf algebra $H$ is an algebra anti-homomorphism: $S(ab) = S(b) S(a)$. Hint: in the convolution algebra $\mathrm{Hom}(H \otimes H, H)$, show that both sides are inverses of $\mu$.
5. (B) Let $k[\mathbb{Z}/n]^*$ be the dual of the group algebra of a cyclic group. Show that it is the algebra $k^n$ of functions with pointwise product. Hint: the example of the coalgebra $k[X]$.
6. (C) Prove that the group-like elements $\{c \in H : \Delta(c) = c \otimes c, \varepsilon(c) = 1\}$ of a Hopf algebra form a group under multiplication, with inverse $S(c)$. Over a field, show that the group-like elements of $k[G]$ are exactly the elements of $G$. Hint: for the second part, compare the coefficients of $\Delta(\sum a_g g)$ and $(\sum a_g g) \otimes (\sum a_h h)$.
7. (C) Show that a bialgebra is a monoid in the monoidal category of coalgebras, and also a comonoid in the monoidal category of algebras. Hint: the condition that $\mu$ is a coalgebra map is the same as the condition that $\Delta$ is an algebra map.

### Notes and history

Hopf algebras appear in Hopf's work of 1941 on the cohomology of Lie groups, where the cup product and the map induced by the group multiplication give the two structures. Milnor and Moore gave the algebraic theory in 1965, and Sweedler wrote a standard text on Hopf algebras in 1969. The convolution argument for the antipode is standard and is in Sweedler's book.

The Mathlib files are by these authors, read from their headers: `AlgCat.Basic` by Kim Morrison; `CommAlgCat.Basic` by Yaël Dillies, Christian Merten, Michał Mrugała and Andrew Yang; `CoalgCat.Basic`, `CoalgCat.ComonEquivalence`, `BialgCat.Basic` and `HopfAlgCat.Basic` by Amelia Livingston.

### Reference

<?reference?>
