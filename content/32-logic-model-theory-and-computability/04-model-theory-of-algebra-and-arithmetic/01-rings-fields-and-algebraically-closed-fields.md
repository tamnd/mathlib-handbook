---
title: Rings, fields and algebraically closed fields
kind: theory
modules:
  - Mathlib.ModelTheory.Algebra.Ring.Basic
  - Mathlib.ModelTheory.Algebra.Ring.Definability
  - Mathlib.ModelTheory.Algebra.Ring.FreeCommRing
  - Mathlib.ModelTheory.Algebra.Field.Basic
  - Mathlib.ModelTheory.Algebra.Field.CharP
  - Mathlib.ModelTheory.Algebra.Field.IsAlgClosed
explains:
  E3: [FirstOrder.Language.ring, FirstOrder.ringFunc, FirstOrder.Ring.CompatibleRing, FirstOrder.Ring.termOfFreeCommRing, FirstOrder.Ring.mvPolynomial_zeroLocus_definable, FirstOrder.Field.FieldAxiom, FirstOrder.Language.Theory.field, FirstOrder.Language.Theory.fieldOfChar, FirstOrder.Field.charP_iff_model_fieldOfChar, FirstOrder.Field.genericMonicPolyHasRoot, FirstOrder.Language.Theory.ACF, FirstOrder.Field.ACF_categorical, FirstOrder.Field.ACF_isComplete, FirstOrder.Field.ACF_zero_realize_iff_infinite_ACF_prime_realize]
  E2: [FirstOrder.Ring.realize_add, FirstOrder.Ring.realize_mul, FirstOrder.Ring.realize_neg, FirstOrder.Ring.realize_zero, FirstOrder.Ring.realize_one, FirstOrder.Ring.card_ring, FirstOrder.Ring.compatibleRingOfRing, FirstOrder.Ring.languageEquivEquivRingEquiv, FirstOrder.Ring.compatibleRingOfRingStructure, FirstOrder.Ring.realize_termOfFreeCommRing, FirstOrder.Field.FieldAxiom.toSentence, FirstOrder.Field.FieldAxiom.toProp, FirstOrder.Field.FieldAxiom.realize_toSentence_iff_toProp, FirstOrder.Field.fieldOfModelField, FirstOrder.Field.compatibleRingOfModelField, FirstOrder.Field.eqZero, FirstOrder.Field.realize_eqZero, FirstOrder.Field.charP_of_model_fieldOfChar, FirstOrder.Field.genericMonicPoly, FirstOrder.Field.realize_genericMonicPolyHasRoot, FirstOrder.Field.isAlgClosed_of_model_ACF, FirstOrder.Field.fieldOfModelACF, FirstOrder.Field.ACF_isSatisfiable, FirstOrder.Field.finite_ACF_prime_not_realize_of_ACF_zero_realize, FirstOrder.Field.ACF_zero_realize_iff_finite_ACF_prime_not_realize]
  E1: auto
families: []
requires: [V06.C01, V06.C04, V11.C03, V32.C01, V32.C02, V32.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Rings, fields and algebraically closed fields

### Overview

A ring is a set with two operations and two constants, so it is a structure in a language with five symbols. A field is a ring that satisfies one more first-order sentence, and an algebraically closed field is a field that satisfies one more sentence for each degree. Model theory then gives facts about all algebraically closed fields of one characteristic at the same time. The theory $\mathrm{ACF}_p$ is complete, so a sentence in the language of rings is true in one algebraically closed field of characteristic $p$ if and only if it is true in all of them. The Lefschetz principle follows: a sentence true in $\mathbb{C}$ is true in each algebraically closed field of sufficiently large prime characteristic.

This section defines the language of rings and the structure of a ring, turns polynomials into terms, proves that the zero locus of finitely many polynomials is definable, writes the axioms of fields, of fields of characteristic $p$ and of algebraically closed fields, and proves completeness of $\mathrm{ACF}_p$ and the Lefschetz principle.

### Definitions

**Definition (Language of rings).** The language of rings has the binary function symbols $+$ and $\cdot$, the unary function symbol $-$, the constant symbols $0$ and $1$, and no relation symbols.

**Definition (Compatible ring structure).** Let $R$ carry operations $+$, $\cdot$, $-$ and constants $0$, $1$. A structure on $R$ for the language of rings is compatible if each symbol is interpreted as the operation or constant of the same name.

The compatibility is a separate datum because a type can carry two unrelated structures. For a compatible structure, the realization of a term $t_1 + t_2$ is the sum of the realizations, and the same holds for the other symbols.

**Definition (Field axioms).** The theory of fields is the set of the nine sentences $$\begin{aligned} &\forall x \forall y \forall z\, ((x + y) + z = x + (y + z)), \quad \forall x\, (0 + x = x), \quad \forall x\, (-x + x = 0),\\ &\forall x \forall y \forall z\, ((x y) z = x (y z)), \quad \forall x \forall y\, (x y = y x), \quad \forall x\, (1 \cdot x = x),\\ &\forall x\, (\neg (x = 0) \to \exists y\, (x y = 1)), \quad \forall x \forall y \forall z\, (x (y + z) = x y + x z), \quad \exists x \exists y\, \neg (x = y). \end{aligned}$$

**Definition (Fields of characteristic p).** For $n \in \mathbb{N}$, let $\underline{n}$ be the term $1 + \cdots + 1$ with $n$ summands and $\underline{0} = 0$. The theory $\mathrm{Fld}_p$ is the theory of fields together with: the sentences $\neg (\underline{q} = 0)$ for all primes $q$ if $p = 0$; the sentence $\underline{p} = 0$ if $p$ is prime; the sentence $\bot$ otherwise.

**Definition (Algebraically closed fields).** For $n \geq 1$, the root sentence of degree $n$ is $$\rho_n = \forall a_0 \cdots \forall a_{n-1} \exists x\, (x^n + a_{n-1} x^{n-1} + \cdots + a_1 x + a_0 = 0),$$ where $x^k$ abbreviates a product of $k$ copies of $x$. The theory $\mathrm{ACF}_p$ is $\mathrm{Fld}_p \cup \{\rho_n : n \geq 1\}$.

### Theorems and proofs

**Proposition (Commutativity of addition).** Each model of the theory of fields satisfies $\forall x \forall y\, (x + y = y + x)$.

*Proof.* The first three axioms make $(K, +, 0)$ a group with left identity and left inverses, and such a group also has $x + 0 = x$ and $x + (-x) = 0$. Commutativity of multiplication and the left distributive law give $(y + z) x = y x + z x$, and $x \cdot 1 = x$. Expand $(1 + 1)(a + b)$ in two ways. The left law gives $(1 + 1) a + (1 + 1) b = a + a + b + b$. The right law gives $1 (a + b) + 1 (a + b) = a + b + a + b$. So $a + (a + b) + b = a + (b + a) + b$, and cancellation of $a$ on the left and of $b$ on the right gives $a + b = b + a$. $\square$

**Proposition (Models of the theory of fields).** Let $K$ carry a compatible structure. Then $K$ is a model of the theory of fields if and only if $K$, with its operations, is a field. Each model of the theory of fields carries a field structure that makes its structure compatible.

*Proof.* With a compatible structure, the realization of each axiom is the statement of the same name about the operations of $K$. These nine statements, with commutativity of addition from the proposition above, are the axioms of a field. For the second statement, define $x + y$, $x y$, $-x$, $0$ and $1$ as the interpretations of the symbols. The structure is then compatible by construction, and the first statement applies. $\square$

**Proposition (Characteristic).** Let $K$ be a field with a compatible structure. Then $K \models \mathrm{Fld}_p$ if and only if $K$ has characteristic $p$.

*Proof.* The realization of $\underline{n}$ in $K$ is the element $n \cdot 1_K$. The characteristic of a field is $0$ or a prime (Volume 6). If $p$ is prime, $K \models \underline{p} = 0$ if and only if $p \cdot 1_K = 0$, which for a prime $p$ says that the characteristic is $p$. If $p = 0$, then $K \models \neg(\underline{q} = 0)$ for all primes $q$ if and only if the characteristic is not a prime, that is, it is $0$. If $p$ is neither, no structure satisfies $\bot$, and no field has characteristic $p$. $\square$

**Lemma (Polynomials are terms).** For each element $f$ of the free commutative ring on a set $\alpha$ there is a term $t_f$ of the language of rings in the variables $\alpha$ such that $t_f^R[v] = f(v)$ for each commutative ring $R$ with a compatible structure and each $v \colon \alpha \to R$.

*Proof.* The free commutative ring is generated by the variables $X_a$ under $+$, $\cdot$, $-$, $0$ and $1$, so each element is the image of a term under the evaluation map from terms to the free ring. Choose such a term $t_f$. Both $t \mapsto t^R[v]$ and the composite of the evaluation with $f \mapsto f(v)$ are compatible with the five operations and agree on variables, so by induction on $t$ they agree. $\square$

**Theorem (Zero loci are definable).** Let $K$ be a field with a compatible structure and let $S$ be a finite set of polynomials in $K[X_i : i \in \iota]$. Let $A$ be the set of their coefficients. Then the zero locus $\{v \in K^{\iota} : f(v) = 0 \text{ for all } f \in (S)\}$ of the ideal generated by $S$ is $A$-definable.

*Proof.* A point $v$ is a zero of each element of the ideal $(S)$ if and only if it is a zero of each $f \in S$, because evaluation at $v$ is a ring homomorphism. Each $f \in S$ is a polynomial with integer coefficients in the variables $X_i$ and the coefficients of $f$, so the lemma gives a term $t_f$ of $L[[A]]$ with $t_f^K[v] = f(v)$, the coefficients being constants. The formula $\bigwedge_{f \in S} t_f = 0$ defines the zero locus. $\square$

**Proposition (Models of ACF).** Let $K$ be a field of characteristic $p$ with a compatible structure. Then $K \models \mathrm{ACF}_p$ if and only if $K$ is algebraically closed. The theory $\mathrm{ACF}_p$ is satisfiable when $p$ is $0$ or prime, and its models are infinite.

*Proof.* The sentence $\rho_n$ says that each monic polynomial of degree $n$ has a root. A field is algebraically closed if and only if each monic polynomial of positive degree has a root. An algebraic closure of $\mathbb{Q}$ or of $\mathbb{F}_p$ is a model (Volume 11). A finite field $\{a_1, \dots, a_k\}$ is not algebraically closed, since $(x - a_1) \cdots (x - a_k) + 1$ has no root. $\square$

**Theorem (Categoricity of ACF).** Let $\kappa$ be an uncountable cardinal. Two algebraically closed fields of the same characteristic and cardinality $\kappa$ are isomorphic. So $\mathrm{ACF}_p$ is $\kappa$-categorical.

*Proof.* Let $K$ have characteristic $p$, prime field $F$, and a transcendence basis $B$ over $F$. Then $K$ is algebraic over $F(B)$. An algebraic extension of a field $E$ has at most $\max(|E|, \aleph_0)$ elements, since each element is a root of one of the polynomials over $E$, each with finitely many roots. As $F$ is countable, $|F(B)| \leq \max(|B|, \aleph_0)$, so $\kappa = |K| \leq \max(|B|, \aleph_0)$. As $\kappa > \aleph_0$ and $|B| \leq \kappa$, this gives $|B| = \kappa$. Let $K'$ be a second such field, with basis $B'$ of size $\kappa$ over its prime field $F' \cong F$. A bijection $B \to B'$ and the isomorphism $F \cong F'$ give an isomorphism $F(B) \cong F'(B')$. Both $K$ and $K'$ are algebraic closures of these fields, and algebraic closures are unique up to isomorphism (Volume 11), so $K \cong K'$. A ring isomorphism of compatible structures is an isomorphism of structures. $\square$

**Corollary (Completeness of ACF).** For $p$ equal to $0$ or a prime, $\mathrm{ACF}_p$ is complete.

*Proof.* The language has $5$ symbols, so its cardinality is at most $\aleph_1$. The theory is $\aleph_1$-categorical, satisfiable, and has only infinite models. The Łoś-Vaught test of Chapter 2 gives completeness. $\square$

**Theorem (Lefschetz principle).** For a sentence $\varphi$ of the language of rings, these are equivalent: (1) $\mathrm{ACF}_0 \models \varphi$, that is, $\varphi$ holds in $\mathbb{C}$; (2) $\mathrm{ACF}_p \models \varphi$ for all but finitely many primes $p$; (3) $\mathrm{ACF}_p \models \varphi$ for infinitely many primes $p$.

*Proof.* (1) implies (2). By compactness (Chapter 2), a finite subset $T_0 \subseteq \mathrm{ACF}_0$ has $T_0 \models \varphi$. It contains finitely many sentences $\neg(\underline{q} = 0)$, say for $q \in Q$. Let $p$ be a prime outside $Q$. A model of $\mathrm{ACF}_p$ satisfies $\neg(\underline{q} = 0)$ for each prime $q \neq p$, and it satisfies the field axioms and each $\rho_n$, so it is a model of $T_0$ and of $\varphi$. (2) implies (3), because there are infinitely many primes. (3) implies (1). If $\mathrm{ACF}_0 \not\models \varphi$, then $\mathrm{ACF}_0 \models \neg\varphi$ by completeness, so by the first step $\mathrm{ACF}_p \models \neg \varphi$ for all but finitely many $p$. As $\mathrm{ACF}_p$ is satisfiable, it does not also give $\varphi$, so $\varphi$ holds for only finitely many $p$. Last, $\mathbb{C}$ is a model of the complete theory $\mathrm{ACF}_0$, so $\mathbb{C} \models \varphi$ if and only if $\mathrm{ACF}_0 \models \varphi$. $\square$

### Examples

**Example (A sentence and its primes).** Let $\varphi$ be $\neg (1 + 1 = 0) \wedge \exists x\, (x \cdot x = 1 + 1)$. It holds in $\mathbb{C}$, as $\sqrt 2 \in \mathbb{C}$. In characteristic $p$ the second conjunct always holds, by $\rho_2$, and the first fails exactly for $p = 2$. So $\varphi$ holds in $\mathrm{ACF}_p$ for every prime except $2$, as the Lefschetz principle predicts.

**Example (The unit circle).** In $\mathbb{C}$, the zero locus of $X^2 + Y^2 - 1$ is defined by the formula $x \cdot x + y \cdot y + -(1) = 0$ with no parameters, since its coefficients $1$ and $-1$ are terms. The zero locus of $X - \pi Y$ needs the parameter $\pi$, and the theorem gives the formula $x + -(c_\pi \cdot y) = 0$.

**Example (A characteristic without models).** $\mathrm{Fld}_4$ contains $\bot$, so it has no model. This matches the algebra: if $4 \cdot 1 = 0$ in a field, then $(2 \cdot 1)^2 = 0$, so $2 \cdot 1 = 0$, and the characteristic is $2$, not $4$.

**Counterexample (The real numbers).** $\mathbb{R}$ is a model of $\mathrm{Fld}_0$ but not of $\mathrm{ACF}_0$: the instance $a_0 = 1$, $a_1 = 0$ of $\rho_2$ asks for a root of $x^2 + 1$. So the sentence $\forall a \exists x\, (x x + a = 0)$ separates $\mathbb{R}$ from $\mathbb{C}$, and $\mathrm{Fld}_0$ is not complete.

### The library around it

::: mathlib
`FirstOrder.Language.ring` · `Mathlib.ModelTheory.Algebra.Ring.Basic`

`Language.ring` has `Functions := ringFunc` with the constructors `add`, `mul`, `neg`, `zero`, `one`, and no relations, and `card_ring : card Language.ring = 5`. Terms have instances of `Add`, `Mul`, `Neg`, `Zero` and `One`, so `&0 + &1` is a term.

<?decl FirstOrder.Language.ring?>
:::

::: mathlib
`FirstOrder.Ring.CompatibleRing` · `Mathlib.ModelTheory.Algebra.Ring.Basic`

`CompatibleRing R` extends `Language.ring.Structure R` with `funMap_add`, `funMap_mul`, `funMap_neg`, `funMap_zero` and `funMap_one`. The simp lemmas `realize_add`, `realize_mul` and the others compute realizations. `compatibleRingOfRing R` is a definition, not an instance, and `compatibleRingOfRingStructure` goes the other way. `languageEquivEquivRingEquiv` identifies `Language.ring.Equiv R S` with `R ≃+* S`.

<?decl FirstOrder.Ring.CompatibleRing?>
:::

::: mathlib
`FirstOrder.Ring.termOfFreeCommRing` · `Mathlib.ModelTheory.Algebra.Ring.FreeCommRing`

`termOfFreeCommRing p` is a term chosen by `Classical.choose`, and `realize_termOfFreeCommRing` states `(termOfFreeCommRing p).realize v = FreeCommRing.lift v p`.

<?decl FirstOrder.Ring.termOfFreeCommRing?>
:::

::: mathlib
`FirstOrder.Ring.mvPolynomial_zeroLocus_definable` · `Mathlib.ModelTheory.Algebra.Ring.Definability`

For `S : Finset (MvPolynomial ι K)`, the set `zeroLocus K (Ideal.span S)` is `Set.Definable` over `⋃ p ∈ S, p.coeff '' p.support`. The zero locus is `MvPolynomial.zeroLocus` from the Nullstellensatz file.

<?decl FirstOrder.Ring.mvPolynomial_zeroLocus_definable?>
:::

::: mathlib
`FirstOrder.Language.Theory.field` · `Mathlib.ModelTheory.Algebra.Field.Basic`

`Theory.field` is `Set.range FieldAxiom.toSentence`, where `FieldAxiom` has the nine constructors `addAssoc`, `zeroAdd`, `negAddCancel`, `mulAssoc`, `mulComm`, `oneMul`, `existsInv`, `leftDistrib` and `existsPairNE`. `realize_toSentence_iff_toProp` compares each sentence with `FieldAxiom.toProp`. `fieldOfModelField K` builds a `Field K` from a model, and `compatibleRingOfModelField K` makes the structure compatible.

<?decl FirstOrder.Language.Theory.field?>
:::

::: mathlib
`FirstOrder.Language.Theory.fieldOfChar` · `Mathlib.ModelTheory.Algebra.Field.CharP`

`Theory.fieldOfChar p` uses the sentence `eqZero n`, with `realize_eqZero` giving `(n : K) = 0`. The result is `charP_iff_model_fieldOfChar : (Theory.fieldOfChar p).Model K ↔ CharP K p`.

<?decl FirstOrder.Language.Theory.fieldOfChar?>
:::

::: mathlib
`FirstOrder.Language.Theory.ACF` · `Mathlib.ModelTheory.Algebra.Field.IsAlgClosed`

`Theory.ACF p` is `Theory.fieldOfChar p ∪ genericMonicPolyHasRoot '' {n | 0 < n}`, built from `genericMonicPoly n : FreeCommRing (Fin (n + 1))`. The results are `isAlgClosed_of_model_ACF`, `ACF_isSatisfiable`, `ACF_categorical`, `ACF_isComplete` and, for `φ : Language.ring.Sentence`, `ACF_zero_realize_iff_infinite_ACF_prime_realize : Theory.ACF 0 ⊨ᵇ φ ↔ Set.Infinite {p : Nat.Primes | Theory.ACF p ⊨ᵇ φ}`.

<?decl FirstOrder.Language.Theory.ACF?>

<?decl FirstOrder.Field.ACF_isComplete?>
:::

::: mathlib
`ax_grothendieck_univ` · `Mathlib.FieldTheory.AxGrothendieck`

The Ax-Grothendieck theorem: over an algebraically closed field, an injective polynomial map `K^ι → K^ι` with `Finite ι` is surjective. The proof proves it for algebraic extensions of finite fields and moves it to all characteristics with the Lefschetz principle. `ax_grothendieck_of_definable` extends it to definable sets.

<?decl ax_grothendieck_univ?>
:::

Common errors of a learner: The first error is to assume that a `Field K` instance gives `Language.ring.Structure K`; it does not, and a proof must introduce `compatibleRingOfRing K` with `letI`. The second error is to forget that `Theory.fieldOfChar 4` is satisfiable by nothing. The third error is to confuse `⊨ᵇ`, consequence from a theory, with `⊨`, truth in one structure. The fourth error is to expect commutativity of addition in `FieldAxiom`; it is a consequence.

### Exercises

1. (A) Write the sentence $\rho_3$ in full, and the formula that defines the set of squares in a field. Hint: $\exists y\, (x = y \cdot y)$.
2. (A) Prove that a finite field is not a model of $\mathrm{ACF}_p$, using one root sentence. Hint: see the proposition on models of ACF.
3. (A) Prove that $\{x : x^3 = 1\}$ is $\emptyset$-definable in each field, and count its points in $\mathbb{C}$ and in an algebraic closure of $\mathbb{F}_3$. Hint: $x^3 - 1 = (x - 1)^3$ in characteristic $3$.
4. (B) Prove that $\mathrm{ACF}_p$ is not $\aleph_0$-categorical. Hint: algebraic closures of $\mathbb{Q}(t)$ and of $\mathbb{Q}(t_1, t_2)$ have different transcendence degrees.
5. (B) Prove that the theory of fields of characteristic $0$ is not finitely axiomatizable. Hint: a finite subset is true in $\mathbb{F}_p$ for large $p$.
6. (C) Prove the Ax-Grothendieck theorem for $\mathbb{C}$ from its case for the algebraic closures of the fields $\mathbb{F}_p$. Hint: for fixed degree, injectivity implies surjectivity is one sentence; apply the Lefschetz principle.

### Notes and history

Tarski proved that the theory of algebraically closed fields of a fixed characteristic is complete and decidable, by quantifier elimination. The proof by categoricity uses the Łoś-Vaught test instead. The principle that algebraic geometry over $\mathbb{C}$ transfers to other algebraically closed fields carries the name of Lefschetz, and the theorem that an injective polynomial map is surjective carries the names of Ax and Grothendieck. The index of this edition has no declaration for quantifier elimination in $\mathrm{ACF}_p$, nor for Chevalley's theorem on constructible sets.

The Mathlib files are by these authors, read from their headers: all files under `Mathlib.ModelTheory.Algebra.Ring` and `Mathlib.ModelTheory.Algebra.Field` by Chris Hughes.

### Reference

<?reference?>
