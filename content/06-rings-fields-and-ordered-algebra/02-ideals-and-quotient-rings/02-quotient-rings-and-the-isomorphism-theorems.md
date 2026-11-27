---
title: Quotient rings and the isomorphism theorems
kind: theory
modules:
  - Mathlib.Algebra.RingQuot
explains:
  E3: []
  E2: [RingQuot, RingQuot.mkRingHom]
  E1: auto
families: []
requires: [V06.C01, V05.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Quotient rings and the isomorphism theorems

### Overview

The ring $\mathbb{Z}/n$ is made from $\mathbb{Z}$ by declaring two integers equal when their difference is a multiple of $n$. The same construction works for each ideal $I$ of each ring $R$: two elements are congruent modulo $I$ when their difference is in $I$, and the classes form a ring $R/I$. The quotient map $R \to R/I$ has kernel $I$, so the ideals are exactly the kernels of ring homomorphisms.

This section builds $R/I$ and proves its universal property: a homomorphism that is zero on $I$ factors uniquely through $R/I$. From the universal property follow the three isomorphism theorems, the correspondence between the ideals of $R/I$ and the ideals of $R$ that contain $I$, and the Chinese remainder theorem: if $I + J = R$, then $R/(I \cap J) \cong R/I \times R/J$.

### Definitions

**Definition (Congruence modulo an ideal).** Let $I$ be a two-sided ideal of a ring $R$. Elements $a, b \in R$ are congruent modulo $I$, written $a \equiv b \pmod I$, if $a - b \in I$. The class of $a$ is the coset $a + I = \{ a + x : x \in I \}$.

This is the congruence modulo the additive subgroup $I$ of Volume 5. So it is an equivalence relation, and $a + I = b + I$ if and only if $a - b \in I$.

**Definition (Quotient ring).** The quotient ring $R/I$ is the set of the cosets $a + I$, with
$$(a + I) + (b + I) = (a + b) + I, \qquad (a + I)(b + I) = a b + I.$$
Its zero is $0 + I = I$ and its unit is $1 + I$. The quotient map is $\pi : R \to R/I$, $\pi(a) = a + I$.

**Theorem (The quotient ring is well defined).** The operations of $R/I$ do not depend on the choice of the representatives. With them $R/I$ is a ring, and $\pi$ is a surjective ring homomorphism with $\ker \pi = I$. If $R$ is commutative, so is $R/I$.

*Proof.* Let $a \equiv a'$ and $b \equiv b'$ modulo $I$. Then $(a + b) - (a' + b') = (a - a') + (b - b') \in I$. For the product,
$$a b - a' b' = a (b - b') + (a - a') b'.$$
The first term is in $I$ since $I$ is a left ideal and $b - b' \in I$. The second term is in $I$ since $I$ is a right ideal and $a - a' \in I$. So $a b \equiv a' b'$.

The additive group $R/I$ is the quotient group of Volume 5. Each remaining axiom is an identity, and it holds in $R/I$ because it holds for the representatives. For example $((a + I)(b + I))(c + I) = (a b) c + I = a (b c) + I = (a + I)((b + I)(c + I))$. The map $\pi$ keeps sums, products and $1$ by the definition of the operations, and it is surjective. Finally $\pi(a) = 0 + I$ if and only if $a \in I$, so $\ker \pi = I$. $\square$

The proof uses both absorption rules. For a left ideal that is not two-sided the product is not well defined, as a counterexample below shows.

::: mathlib
`Ideal.Quotient.mk` · `Mathlib.RingTheory.Ideal.Quotient.Defs`

The quotient ring is written `R ⧸ I` (the symbol is `\quot`, not the slash `/`), and the quotient map is `Ideal.Quotient.mk I : R →+* R ⧸ I`, which needs `[I.IsTwoSided]`. The instance `Ideal.Quotient.commRing` gives the commutative ring structure when `R` is commutative. The rule for equality is `Ideal.Quotient.eq : mk I x = mk I y ↔ x - y ∈ I`, and `Ideal.Quotient.mk_surjective` and `Ideal.mk_ker : ker (mk I) = I` are the rest of the theorem.

<?decl Ideal.Quotient.mk?>
:::

### Theorems and proofs

**Theorem (Universal property).** Let $I$ be a two-sided ideal of $R$ and $f : R \to S$ a ring homomorphism with $I \subseteq \ker f$. Then there is exactly one ring homomorphism $\bar f : R/I \to S$ with $\bar f \circ \pi = f$, that is, $\bar f(a + I) = f(a)$. Its range is $f(R)$, and its kernel is $\ker f / I = \{ a + I : a \in \ker f \}$.

*Proof.* Uniqueness: $\pi$ is surjective, so $\bar f$ is fixed by its values $\bar f(a + I) = f(a)$. Existence: define $\bar f(a + I) = f(a)$. If $a + I = a' + I$, then $a - a' \in I \subseteq \ker f$, so $f(a) = f(a')$. So $\bar f$ is well defined. It keeps the operations because $f$ does: $\bar f((a + I)(b + I)) = f(a b) = f(a) f(b)$, and the same for sums and $1$. The range is $\{ f(a) : a \in R \}$. And $\bar f(a + I) = 0$ if and only if $a \in \ker f$. $\square$

::: mathlib
`Ideal.Quotient.lift` · `Mathlib.RingTheory.Ideal.Quotient.Defs`

The map $\bar f$ is `Ideal.Quotient.lift I f h : R ⧸ I →+* S` with `h : ∀ a ∈ I, f a = 0`, and `Ideal.Quotient.lift_mk` is the equation $\bar f(a + I) = f(a)$. The uniqueness is the extensionality lemma `Ideal.Quotient.ringHom_ext`: two homomorphisms out of `R ⧸ I` are equal when they agree after `mk I`.

<?decl Ideal.Quotient.lift?>
:::

**Theorem (First isomorphism theorem).** Let $f : R \to S$ be a ring homomorphism. Then $R / \ker f \cong f(R)$, by $a + \ker f \mapsto f(a)$. In particular, if $f$ is surjective, then $R / \ker f \cong S$.

*Proof.* Apply the universal property with $I = \ker f$, and view $f$ as a homomorphism onto the subring $f(R)$ of $S$. The map $\bar f : R / \ker f \to f(R)$ is surjective, and its kernel is $\ker f / \ker f$, which is the zero of $R / \ker f$. So $\bar f$ is injective, and it is an isomorphism (Section 1.2: a bijective homomorphism is an isomorphism). $\square$

::: mathlib
`RingHom.quotientKerEquivRange` · `Mathlib.RingTheory.Ideal.Quotient.Operations`

The theorem as `R ⧸ ker f ≃+* f.range`. The surjective form is `RingHom.quotientKerEquivOfSurjective : Function.Surjective f → R ⧸ ker f ≃+* S`. The injective map into `S` is `RingHom.kerLift`.

<?decl RingHom.quotientKerEquivRange?>
:::

**Theorem (Second isomorphism theorem).** Let $A$ be a subring and $I$ an ideal of $R$. Then $A + I = \{ a + x : a \in A, x \in I \}$ is a subring of $R$, $I$ is an ideal of $A + I$, $A \cap I$ is an ideal of $A$, and
$$A / (A \cap I) \cong (A + I) / I.$$

*Proof.* $A + I$ contains $1 = 1 + 0$. For $a, b \in A$ and $x, y \in I$,
$$(a + x) - (b + y) = (a - b) + (x - y), \qquad (a + x)(b + y) = a b + (a y + x b + x y),$$
and the bracket is in $I$ by absorption. So $A + I$ is a subring by the subring test. The set $I$ is contained in $A + I$ and absorbs products with all elements of $R$, so it is an ideal of $A + I$.

Let $\varphi : A \to (A + I)/I$, $\varphi(a) = a + I$. It is the restriction of the quotient map to $A$, so it is a ring homomorphism. It is surjective: $(a + x) + I = a + I = \varphi(a)$ for $x \in I$. Its kernel is $\{ a \in A : a \in I \} = A \cap I$. So $A \cap I$ is an ideal of $A$, as a kernel, and the first isomorphism theorem gives the isomorphism. $\square$

Mathlib has no name for this theorem in the form for subrings. A proof in Lean applies `RingHom.quotientKerEquivOfSurjective` to the map $\varphi$ above. For two ideals $I$ and $J$ of a commutative ring the second theorem takes the form $(R/I)/\pi(J) \cong R/(I + J)$, which is `DoubleQuot.quotQuotEquivQuotSup`.

**Theorem (Third isomorphism theorem).** Let $I \subseteq J$ be two-sided ideals of $R$. Then $J/I = \{ a + I : a \in J \}$ is an ideal of $R/I$, and
$$(R/I)/(J/I) \cong R/J.$$

*Proof.* The universal property, applied to the quotient map $R \to R/J$, which is zero on $I \subseteq J$, gives a homomorphism $\psi : R/I \to R/J$ with $\psi(a + I) = a + J$. It is surjective. Its kernel is $J/I$ by the universal property. So $J/I$ is an ideal, as a kernel, and the first isomorphism theorem gives the isomorphism. $\square$

::: mathlib
`DoubleQuot.quotQuotEquivQuotOfLE` · `Mathlib.RingTheory.Ideal.Quotient.Operations`

The third theorem for a commutative ring, `I ≤ J → (R ⧸ I) ⧸ map (mk I) J ≃+* R ⧸ J`. The ideal `J/I` of the text is `Ideal.map (Ideal.Quotient.mk I) J`, the image of $J$, which is an ideal since `mk I` is surjective.

<?decl DoubleQuot.quotQuotEquivQuotOfLE?>
:::

**Theorem (Correspondence theorem).** Let $I$ be an ideal of a commutative ring $R$ and $\pi : R \to R/I$ the quotient map. The maps $J \mapsto \pi(J) = J/I$ and $K \mapsto \pi^{-1}(K)$ are inverse bijections between the ideals $J$ of $R$ with $I \subseteq J$ and the ideals $K$ of $R/I$. Both keep the inclusion.

*Proof.* By Section 1, $\pi(J)$ is an ideal since $\pi$ is surjective, and $\pi^{-1}(K)$ is an ideal that contains $\ker \pi = I$. Since $\pi$ is surjective, $\pi(\pi^{-1}(K)) = K$. For $J \supseteq I$, clearly $J \subseteq \pi^{-1}(\pi(J))$. Conversely, if $\pi(a) \in \pi(J)$, then $\pi(a) = \pi(b)$ for some $b \in J$, so $a - b \in I \subseteq J$ and $a \in J$. Hence $\pi^{-1}(\pi(J)) = J$. Images and preimages keep the inclusion. $\square$

::: mathlib
`Ideal.relIsoOfSurjective` · `Mathlib.RingTheory.Ideal.Maps`

The theorem for each surjective `f`, as an order isomorphism `Ideal S ≃o {p // comap f ⊥ ≤ p}`. Here `comap f ⊥` is the kernel. So the correspondence also matches sums and intersections.

<?decl Ideal.relIsoOfSurjective?>
:::

**Theorem (Chinese remainder theorem).** Let $I$ and $J$ be ideals of a commutative ring $R$ with $I + J = R$. Then
$$R/(I \cap J) \cong R/I \times R/J, \qquad a + (I \cap J) \mapsto (a + I, a + J),$$
and $I \cap J = I J$.

*Proof.* Let $\varphi : R \to R/I \times R/J$, $\varphi(a) = (a + I, a + J)$. Its components are quotient maps, so $\varphi$ is a ring homomorphism into the product ring. Its kernel is the set of the $a$ with $a \in I$ and $a \in J$, so $\ker \varphi = I \cap J$.

Surjectivity: write $1 = x + y$ with $x \in I$ and $y \in J$. Then $y = 1 - x \equiv 1 \pmod I$ and $y \equiv 0 \pmod J$. In the same way $x \equiv 0 \pmod I$ and $x \equiv 1 \pmod J$. For given $b, c \in R$ let $a = b y + c x$. Then
$$a \equiv b \cdot 1 + c \cdot 0 = b \pmod I, \qquad a \equiv b \cdot 0 + c \cdot 1 = c \pmod J.$$
So $\varphi(a) = (b + I, c + J)$. The first isomorphism theorem gives the isomorphism. The equality $I \cap J = I J$ is part (4) of the theorem on products in Section 1. $\square$

By induction the theorem extends to pairwise coprime ideals $I_1, \dots, I_n$ (Exercise 10).

::: mathlib
`Ideal.quotientInfEquivQuotientProd` · `Mathlib.RingTheory.Ideal.Quotient.Operations`

The theorem for two ideals, `IsCoprime I J → R ⧸ I ⊓ J ≃+* (R ⧸ I) × R ⧸ J`. Mathlib states coprimality as `IsCoprime I J`, that is $a I + b J = 1$ in the semiring of ideals, and `Ideal.isCoprime_iff_sup_eq` turns it into `I ⊔ J = ⊤`. The form for a finite family is `Ideal.quotientInfRingEquivPiQuotient`, and the form for $\mathbb{Z}/m n$ is `ZMod.chineseRemainder` (Chapter 4).

<?decl Ideal.quotientInfEquivQuotientProd?>
:::

### Examples

**Example (The Gaussian integers modulo $2 + i$).** Let $I = (2 + i)$ in $\mathbb{Z}[i]$ and let $\chi : \mathbb{Z} \to \mathbb{Z}[i]/I$ be the composite of the inclusion and the quotient map. Since $i \equiv -2 \pmod I$, each class $a + b i + I$ equals $(a - 2 b) + I = \chi(a - 2 b)$, so $\chi$ is surjective. Its kernel is $\mathbb{Z} \cap I$, an ideal of $\mathbb{Z}$. It contains $5 = (2 + i)(2 - i)$, and it does not contain $1$, by the computation in Section 1. The ideals of $\mathbb{Z}$ that contain $5$ are $(1)$ and $(5)$, since $5$ is prime. So $\ker \chi = (5)$, and the first isomorphism theorem gives
$$\mathbb{Z}/5 \cong \mathbb{Z}[i]/(2 + i), \qquad a + b i + (2 + i) \leftrightarrow [a - 2 b].$$
For example $3 + 4 i$ maps to $[3 - 8] = [0]$, and indeed $3 + 4 i = (2 + i)(2 + i)$. The class of $i$ is $[-2] = [3]$, and $[3]^2 = [9] = [-1]$, as it must be.

**Example (Two congruences).** The ideals $(4)$ and $(9)$ of $\mathbb{Z}$ are coprime, with $1 = 9 + (-2) \cdot 4$. Take $x = -8 \in (4)$ and $y = 9 \in (9)$. Then $y \equiv 1 \pmod 4$, $y \equiv 0 \pmod 9$, $x \equiv 0 \pmod 4$ and $x \equiv 1 \pmod 9$. To solve $a \equiv 3 \pmod 4$ and $a \equiv 5 \pmod 9$, the proof gives $a = 3 y + 5 x = 27 - 40 = -13 \equiv 23 \pmod{36}$. Check: $23 = 5 \cdot 4 + 3$ and $23 = 2 \cdot 9 + 5$. The theorem gives $\mathbb{Z}/36 \cong \mathbb{Z}/4 \times \mathbb{Z}/9$.

**Counterexample (Coprimality is needed).** The ideals $(2)$ and $(2)$ of $\mathbb{Z}$ are not coprime: $(2) + (2) = (2)$. Here $(2) \cap (2) = (2)$, and $\mathbb{Z}/2$ is not isomorphic to $\mathbb{Z}/2 \times \mathbb{Z}/2$, which has four elements. For $(2)$ and $(4)$ the map $\mathbb{Z}/4 \to \mathbb{Z}/2 \times \mathbb{Z}/4$ is not surjective either. And $\mathbb{Z}/4 \not\cong \mathbb{Z}/2 \times \mathbb{Z}/2$, since $[1]$ has additive order $4$ in $\mathbb{Z}/4$ but each element of $\mathbb{Z}/2 \times \mathbb{Z}/2$ has order at most $2$.

**Example (A quotient of $\mathbb{Z}/12$).** The third theorem with $(12) \subseteq (4)$ gives $(\mathbb{Z}/12)/([4]) \cong \mathbb{Z}/4$: the cosets of $([4]) = \{[0], [4], [8]\}$ are the four sets $\{[r], [r + 4], [r + 8]\}$, one for each class $r$ modulo $4$.

**Example (A preview: $\mathbb{R}[X]/(X^2 + 1) \cong \mathbb{C}$).** The evaluation $\mathbb{R}[X] \to \mathbb{C}$, $p \mapsto p(i)$, is a ring homomorphism. It is surjective, since $a + b X \mapsto a + b i$. Its kernel contains $X^2 + 1$. Division with remainder by $X^2 + 1$ (Chapter 5) writes each $p$ as $(X^2 + 1) q + a + b X$, and $p(i) = a + b i$ is zero only if $a = b = 0$. So the kernel is $(X^2 + 1)$, and the first isomorphism theorem gives $\mathbb{R}[X]/(X^2 + 1) \cong \mathbb{C}$. Volume 11 builds field extensions in this way, with `AdjoinRoot`.

**Counterexample (Quotient by a left ideal).** In $M_2(\mathbb{R})$ let $L$ be the left ideal of the matrices with second column zero (Section 1). Then $E_{11} \equiv 0 \pmod L$. If the product were well defined on the cosets, then $E_{11} E_{12} \equiv 0 \cdot E_{12} = 0$. But $E_{11} E_{12} = E_{12} \notin L$. So the cosets of $L$ do not form a ring with the induced product. They form a left module over $M_2(\mathbb{R})$ (Volume 7).

### The library around it

Mathlib has two constructions of a quotient ring. The main one is `R ⧸ I` for an ideal, defined as the quotient module `R ⧸ I` of linear algebra with the ring structure added. All of Volume 9 uses it. The second is `RingQuot r`, the quotient by the smallest ring congruence that contains an arbitrary relation `r`. It works for noncommutative semirings, and Mathlib uses it to build the tensor algebra and the Clifford algebras. For a commutative ring the two agree: `RingQuot.ringQuotEquivIdealQuotient r : RingQuot r ≃+* R ⧸ Ideal.ofRel r`.

::: mathlib
`RingQuot` · `Mathlib.Algebra.RingQuot`

The quotient `RingQuot r` of a semiring by the ring congruence generated by `r : R → R → Prop`. The quotient map is `RingQuot.mkRingHom r : R →+* RingQuot r`, with `RingQuot.mkRingHom_rel : r x y → mkRingHom r x = mkRingHom r y` and `RingQuot.mkRingHom_surjective`. The universal property is `RingQuot.lift`, and the algebra form of the map is `RingQuot.mkAlgHom`.

<?decl RingQuot?>
:::

The isomorphisms of the section are terms of type `≃+*`, so they compose with `RingEquiv.trans` and invert with `RingEquiv.symm`.

Common errors of a learner:

- The quotient symbol is `⧸`, typed `\quot`. The slash `/` is the division, and `R / I` gives a confusing error.
- To show that a class `Ideal.Quotient.mk I a` is zero, rewrite it as `a ∈ RingHom.ker (Ideal.Quotient.mk I)` with `RingHom.mem_ker`, and then use `Ideal.mk_ker`.
- `Ideal.Quotient.lift` needs the proof that `f` vanishes on `I`, not on the kernel of `mk`. Pass `fun a ha => ...` with `ha : a ∈ I`.
- The isomorphism `R ⧸ ker f ≃+* f.range` lands in `↥f.range`, a subtype. To land in `S`, use the surjective form or compose with `Subring.subtype`.

### Exercises

1. (A) Write the addition and multiplication tables of $\mathbb{Z}[i]/(2)$. Show that it has four elements and a nonzero element whose square is $0$.
2. (A) Find all $a \in \mathbb{Z}$ with $a \equiv 2 \pmod 5$ and $a \equiv 3 \pmod 7$, with the method of the proof of the Chinese remainder theorem.
3. (A) Show that $\mathbb{Z}[X]/(X) \cong \mathbb{Z}$ and $\mathbb{Z}[X]/(2, X) \cong \mathbb{Z}/2$. Hint: evaluation at $0$, then the third theorem.
4. (A) Let $I \subseteq R$ be an ideal. Show that $R/I$ is the zero ring if and only if $I = R$.
5. (B) Show that $\mathbb{Z}[i]/(3)$ is a field with nine elements. Hint: show that $a + b i \mapsto (a, b)$ gives nine classes, and that $a^2 + b^2 \not\equiv 0 \pmod 3$ unless $a \equiv b \equiv 0$.
6. (B) Show that $\mathbb{Z}[i]/(1 + 2i) \cong \mathbb{Z}/5$, and describe the isomorphism on $i$. Compare with the example for $2 + i$.
7. (B) Let $R$ be commutative and $I, J$ coprime ideals. Show that $I^m$ and $J^n$ are coprime for all $m, n \ge 1$. Hint: raise $1 = x + y$ to the power $m + n - 1$.
8. (B) Show that $\mathbb{R}[X]/(X^2 - 1) \cong \mathbb{R} \times \mathbb{R}$, by the Chinese remainder theorem for $(X - 1)$ and $(X + 1)$.
9. (C) Let $f : R \to S$ be a surjective homomorphism of commutative rings with kernel $K$. Show that the ideals of $S$ correspond to the ideals of $R$ that contain $K$, and that $S/J \cong R/f^{-1}(J)$ for each ideal $J$ of $S$.
10. (C) Let $R$ be commutative and $I_1, \dots, I_n$ pairwise coprime ideals. Prove that $R/(I_1 \cdots I_n) \cong R/I_1 \times \dots \times R/I_n$. Hint: show first that $I_1$ and $I_2 \cdots I_n$ are coprime, then use induction.

### Notes and history

Congruences modulo an integer go back to Gauss, *Disquisitiones Arithmeticae* (1801), and the Chinese remainder theorem for integers to Sunzi's *Mathematical Classic* (third to fifth century). Kronecker built field extensions as quotients of polynomial rings in the 1880s. The isomorphism theorems for rings and modules were stated in general by Emmy Noether in the 1920s, and van der Waerden's *Moderne Algebra* (1930) gave them their textbook form. Standard references are Dummit and Foote, *Abstract Algebra*, Section 7.3 for the isomorphism theorems and Section 7.6 for the Chinese remainder theorem, and Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapter 1.

In Mathlib the quotient by an ideal was defined in Lean 3 by Kenny Lau, Chris Hughes and Mario Carneiro, as a quotient module. The file `Mathlib/Algebra/RingQuot.lean` was written for the construction of the tensor algebra.

### Reference

<?reference?>
