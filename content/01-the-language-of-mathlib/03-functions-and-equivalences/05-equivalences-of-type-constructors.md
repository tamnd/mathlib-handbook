---
title: Equivalences of type constructors
kind: api
modules:
  - Mathlib.Logic.Equiv.Basic
  - Mathlib.Logic.Equiv.Prod
  - Mathlib.Logic.Equiv.Sum
  - Mathlib.Logic.Equiv.Option
  - Mathlib.Logic.Equiv.Sigma
  - Mathlib.Logic.Equiv.Set
  - Mathlib.Logic.Embedding.Set
  - Mathlib.Logic.Equiv.Embedding
  - Mathlib.Logic.Equiv.Functor
explains:
  E2: [Equiv.sumArrowEquivProdArrow, Equiv.prodSumDistrib, Equiv.sigmaFiberEquiv, Equiv.swap_swap, Equiv.removeNone_optionCongr, Equiv.Set.sumCompl, Equiv.ofInjective, Equiv.image_compl]
  E1: auto
families: []
requires: [V01.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Equivalences of type constructors

### Overview

The section on equivalences and embeddings defined the structure `α ≃ β` and its operations `Equiv.refl`, `Equiv.symm` and `Equiv.trans`. The modules of this section supply the instances: the canonical isomorphisms between types built from products, sums, options, dependent pairs, dependent functions, subtypes and sets. A textbook writes $A \times (B \sqcup C) \cong (A \times B) \sqcup (A \times C)$ and then identifies the two sides. Mathlib gives the isomorphism a name, here `Equiv.prodSumDistrib`, and transports results along it.

The modules also make each type constructor act on equivalences. From $e : \alpha_1 \simeq \alpha_2$ and $e' : \beta_1 \simeq \beta_2$ they build $\alpha_1 \times \beta_1 \simeq \alpha_2 \times \beta_2$, $\alpha_1 \oplus \beta_1 \simeq \alpha_2 \oplus \beta_2$, $\mathrm{Option}\ \alpha_1 \simeq \mathrm{Option}\ \alpha_2$, and so on. In the language of categories, each constructor is a functor on the groupoid of types and equivalences. The last modules treat embeddings into sets and the equivalences between types of embeddings.

The reader needs the subtypes, products, sums and sigma types of Chapter 2. Most equivalences of this section are explicit structures, so their inverses have formulas.

### The library around it

#### The naming pattern

The names follow a small set of rules, and a reader who knows the rules can guess most names.

1. A name that ends in `Congr` is the action of a type constructor on equivalences: `Equiv.prodCongr`, `Equiv.sumCongr`, `Equiv.optionCongr`, `Equiv.piCongrRight`, `Equiv.subtypeEquiv`. The permutation versions live in the namespace `Equiv.Perm`, for example `Equiv.Perm.sumCongr`.
2. A name that ends in `Comm` or `Assoc` is a symmetry or an associativity: `Equiv.prodComm`, `Equiv.prodAssoc`, `Equiv.sumComm`, `Equiv.sumAssoc`.
3. A name that contains `Equiv` in the middle reads from left to right as the type of the result: `Equiv.sumArrowEquivProdArrow : (α ⊕ β → γ) ≃ (α → γ) × (β → γ)`.
4. Units and empty types appear in the name: `Equiv.prodPUnit`, `Equiv.punitProd`, `Equiv.prodEmpty`, `Equiv.emptyProd`, `Equiv.sumEmpty`, `Equiv.emptySum`. The versions with `Unique` and `IsEmpty` arguments, `Equiv.prodUnique` and `Equiv.sumEmpty`, accept any type with one element or with none.

Most definitions carry the attribute `simps`, which generates the lemmas `_apply` and `_symm_apply`. For example `Equiv.prodComm_apply` states `Equiv.prodComm α β x = x.swap`, and `Equiv.optionCongr_trans` states that a `Congr` construction respects composition. The simp normal form is the value of the function, not the equivalence: `simp` rewrites `Equiv.prodCongr e₁ e₂` to `Prod.map e₁ e₂` by `Equiv.prodCongr_apply`.

#### Products: `Mathlib.Logic.Equiv.Prod`

| Lean name | Statement |
|---|---|
| `Equiv.prodCongr` | `α₁ ≃ α₂ → β₁ ≃ β₂ → α₁ × β₁ ≃ α₂ × β₂` |
| `Equiv.prodComm` | `α × β ≃ β × α` |
| `Equiv.prodAssoc` | `(α × β) × γ ≃ α × β × γ` |
| `Equiv.prodPUnit` | `α × PUnit ≃ α` |
| `Equiv.prodEmpty` | `α × Empty ≃ Empty` |
| `Equiv.curry` | `(α × β → γ) ≃ (α → β → γ)` |
| `Equiv.sumArrowEquivProdArrow` | `(α ⊕ β → γ) ≃ (α → γ) × (β → γ)` |
| `Equiv.boolArrowEquivProd` | `(Bool → α) ≃ α × α` |
| `Equiv.sumProdDistrib` | `(α ⊕ β) × γ ≃ α × γ ⊕ β × γ` |
| `Equiv.subtypeProdEquivProd` | `{c // p c.1 ∧ q c.2} ≃ {a // p a} × {b // q b}` |

In `Equiv.prodCongrLeft` and `Equiv.prodCongrRight` the equivalence on one factor depends on the point of the other factor. The module also has `Equiv.Perm.prodExtendRight`, which applies a permutation of $\beta$ in the fibre over one point $a$ of $\alpha \times \beta$ and fixes the other fibres.

**Theorem (Functions on a sum).** For all types, $(\alpha \oplus \beta \to \gamma) \simeq (\alpha \to \gamma) \times (\beta \to \gamma)$.

*Proof.* Send $f$ to the pair $(f \circ \mathrm{inl}, f \circ \mathrm{inr})$. Send a pair $(g, h)$ to $\mathrm{Sum.elim}\ g\ h$. Then $\mathrm{Sum.elim}\ (f \circ \mathrm{inl})\ (f \circ \mathrm{inr}) = f$, by function extensionality and a case split on the argument. In the other direction, $\mathrm{Sum.elim}\ g\ h \circ \mathrm{inl} = g$ and $\mathrm{Sum.elim}\ g\ h \circ \mathrm{inr} = h$ hold by definition. $\square$

This is the universal property of the sum, stated as an equivalence.

#### Sums: `Mathlib.Logic.Equiv.Sum`

The module has the same algebra for `⊕`: `Equiv.sumCongr`, `Equiv.sumComm`, `Equiv.sumAssoc`, `Equiv.sumSumSumComm`, `Equiv.sumEmpty` and `Equiv.emptySum`. The two distributive laws are `Equiv.prodSumDistrib` and `Equiv.sumProdDistrib`, and their dependent forms are `Equiv.sigmaSumDistrib` and `Equiv.sumSigmaDistrib`. The equivalence `Equiv.sumEquivSigmaBool` writes $\alpha \oplus \beta$ as a sigma type over `Bool`.

**Theorem (Distributivity).** $\alpha \times (\beta \oplus \gamma) \simeq (\alpha \times \beta) \oplus (\alpha \times \gamma)$.

*Proof.* Send $(a, \mathrm{inl}\ b)$ to $\mathrm{inl}\ (a, b)$ and $(a, \mathrm{inr}\ c)$ to $\mathrm{inr}\ (a, c)$. The inverse sends $\mathrm{inl}\ (a, b)$ to $(a, \mathrm{inl}\ b)$ and $\mathrm{inr}\ (a, c)$ to $(a, \mathrm{inr}\ c)$. Both composites are the identity, by a case split on the summand. $\square$

The values are the simp lemmas `Equiv.prodSumDistrib_apply_left` and `Equiv.prodSumDistrib_apply_right`.

A predicate splits a type in two. For a decidable predicate $p$, `Equiv.sumCompl p` is the equivalence $\{a \mid p\ a\} \oplus \{a \mid \lnot p\ a\} \simeq \alpha$. A function splits its domain into fibres:

**Theorem (Decomposition into fibres).** For $f : \alpha \to \beta$, the type $\alpha$ is equivalent to $\Sigma\, y : \beta,\ \{x \mid f(x) = y\}$.

*Proof.* Send $x$ to the pair $\langle f(x), \langle x, \mathrm{rfl}\rangle\rangle$. Send a pair $\langle y, \langle x, h\rangle\rangle$ to $x$. The composite on $\alpha$ is the identity by definition. For the other composite, start from $\langle y, \langle x, h\rangle\rangle$ with $h : f(x) = y$. Its image is $\langle f(x), \langle x, \mathrm{rfl}\rangle\rangle$. Substitute $y := f(x)$ by $h$: then $h$ becomes $\mathrm{rfl}$, by proof irrelevance, and the two pairs are equal. $\square$

In Mathlib the equivalence is `Equiv.sigmaFiberEquiv f`, in the direction from the sigma type to $\alpha$. The module also has `Equiv.Perm.sumCongr`, the permutation of $\alpha \oplus \beta$ that acts by two given permutations on the summands.

#### Options: `Mathlib.Logic.Equiv.Option`

The type `Option α` is $\alpha$ with one new point `none`. The equivalence `Equiv.optionEquivSumPUnit` makes this exact: `Option α ≃ α ⊕ PUnit`. The functorial map `Equiv.optionCongr e` acts by `Option.map e`, by `Equiv.optionCongr_apply`. An equivalence $e : \mathrm{Option}\ \alpha \simeq \mathrm{Option}\ \beta$ need not send `none` to `none`, but there is still an equivalence $\alpha \simeq \beta$, named `Equiv.removeNone e`. It sends $x$ to the value of $e(\mathrm{some}\ x)$ when this value is of the form $\mathrm{some}\ y$, and to the value of $e(\mathrm{none})$ when $e(\mathrm{some}\ x) = \mathrm{none}$. The lemmas `Equiv.removeNone_some` and `Equiv.removeNone_none` state the two cases, and `Equiv.removeNone_symm` states that the inverse is `Equiv.removeNone e.symm`.

**Theorem.** For $e : \alpha \simeq \beta$, `removeNone (optionCongr e) = e`.

*Proof.* By extensionality, fix $x : \alpha$. The equivalence $\mathrm{optionCongr}\ e$ sends $\mathrm{some}\ x$ to $\mathrm{some}\ (e\ x)$, which is not `none`. So the first case of the definition applies, and the value is $e\ x$. $\square$

So `Equiv.optionCongr` has a left inverse, and `Equiv.optionCongr_injective` follows. Two more constructions remove a point. For $a : \alpha$ with decidable equality, `Equiv.optionSubtypeNe a` is `Option {b // b ≠ a} ≃ α`, which sends `none` to $a$. And `Equiv.optionSubtype x` identifies the equivalences $\mathrm{Option}\ \alpha \simeq \beta$ that send `none` to $x$ with the equivalences $\alpha \simeq \{y \mid y \neq x\}$.

#### Subtypes, pi types, sigma types and swaps: `Mathlib.Logic.Equiv.Basic`

This is the largest module. Its equivalences fall into four families.

*Subtypes.* `Equiv.subtypeEquiv e h` maps $\{a \mid p\ a\}$ to $\{b \mid q\ b\}$ along $e$ when $p\ a \leftrightarrow q\ (e\ a)$. The special case with $e$ the identity is `Equiv.subtypeEquivRight`. `Equiv.subtypeSubtypeEquivSubtypeInter` flattens a subtype of a subtype into a subtype of a conjunction.

*Pi types.* `Equiv.piCongrRight` changes the fibres of a dependent function type, `Equiv.piCongrLeft` changes the index type, and `Equiv.piCongr` does both. `Equiv.piOptionEquivProd` splits a function on `Option α` into its value at `none` and its restriction to `α`.

*Sigma types and fibres.* `Equiv.sigmaAssocProd` reassociates a sigma type over a product. `Equiv.ofFiberEquiv` builds an equivalence $\alpha \simeq \beta$ from equivalences between the fibres of $f : \alpha \to \gamma$ and $g : \beta \to \gamma$ over each point, and `Equiv.ofFiberEquiv_map` states that the result commutes with $f$ and $g$.

*Swaps and permutations.* For a type with decidable equality, `Equiv.swap a b` is the transposition of $a$ and $b$. Its formula is `Equiv.swap_apply_def`:
$$\mathrm{swap}\ a\ b\ x = \begin{cases} b & x = a, \\ a & x = b, \\ x & \text{otherwise.} \end{cases}$$
The lemmas `Equiv.swap_apply_left`, `Equiv.swap_apply_right` and `Equiv.swap_apply_of_ne_of_ne` give the three cases, and `Equiv.swap_comm`, `Equiv.swap_self` and `Equiv.symm_swap` give the symmetries.

**Theorem.** A transposition is an involution: `(swap a b).trans (swap a b) = Equiv.refl α`.

*Proof.* By extensionality, fix $x$. If $x = a$, then $x \mapsto b \mapsto a$. If $x = b$, then $x \mapsto a \mapsto b$. Otherwise $x$ is fixed twice. In each case the result is $x$. $\square$

Other permutations are built from pieces. `Equiv.Perm.subtypeCongr` glues a permutation of $\{a \mid p\ a\}$ and a permutation of $\{a \mid \lnot p\ a\}$. `Equiv.Perm.extendDomain` extends a permutation of a subtype by the identity outside, and `Equiv.Perm.extendDomain_apply_not_subtype` states that the points outside are fixed. `Function.Involutive.toPerm` turns an involution into a permutation.

#### Sets: `Mathlib.Logic.Equiv.Set` and `Mathlib.Logic.Equiv.Sigma`

A set `s : Set α` is a type through the coercion to the subtype `↥s`. The namespace `Equiv.Set` holds the equivalences between these types.

| Lean name | Statement |
|---|---|
| `Equiv.Set.univ` | `↥(Set.univ : Set α) ≃ α` |
| `Equiv.Set.empty` | `↥(∅ : Set α) ≃ Empty` |
| `Equiv.Set.union` | `↥(s ∪ t) ≃ ↥s ⊕ ↥t` for disjoint `s` and `t` |
| `Equiv.Set.insert` | `↥(insert a s) ≃ ↥s ⊕ PUnit` for `a ∉ s` |
| `Equiv.Set.sumCompl` | `↥s ⊕ ↥sᶜ ≃ α` |
| `Equiv.Set.prod` | `↥(s ×ˢ t) ≃ ↥s × ↥t` |
| `Equiv.Set.sigma` | `↥(s.sigma t) ≃ (i : ↥s) × ↥(t i)` |
| `Equiv.Set.powerset` | `↥(𝒫 S) ≃ Set ↥S` |
| `Equiv.Set.image` | `↥s ≃ ↥(f '' s)` for injective `f` |
| `Equiv.image` | `↥s ≃ ↥(e '' s)` for `e : α ≃ β` |
| `Set.equivOfEq` | `↥s ≃ ↥t` for `s = t` |

The module `Mathlib.Logic.Equiv.Sigma` holds only `Equiv.Set.sigma`. Several entries need a decision procedure: `Equiv.Set.union`, `Equiv.Set.insert` and `Equiv.Set.sumCompl` take an instance of `DecidablePred (· ∈ s)`, because the inverse must decide in which summand a point lies.

**Theorem (A set and its complement).** For a set $s \subseteq \alpha$ with decidable membership, $s \oplus s^c \simeq \alpha$.

*Proof.* Send $\mathrm{inl}\ x$ and $\mathrm{inr}\ x$ to the underlying point $x$. Send $x : \alpha$ to $\mathrm{inl}\ \langle x, h\rangle$ if $h : x \in s$, and to $\mathrm{inr}\ \langle x, h\rangle$ if $h : x \notin s$. The test is the decision procedure. Both composites are the identity by a case split on $x \in s$. $\square$

The lemmas `Equiv.Set.sumCompl_apply_inl`, `Equiv.Set.sumCompl_symm_apply_of_mem` and `Equiv.Set.sumCompl_symm_apply_of_notMem` state the values.

**Theorem (An injection onto its range).** If $f : \alpha \to \beta$ is injective, then $\alpha \simeq \mathrm{range}\ f$.

*Proof.* Send $a$ to $\langle f(a), a, \mathrm{rfl}\rangle$. For the inverse, a point of the range is $f(a)$ for some $a$, and $a$ is unique by injectivity. The left inverse `Function.invFun f` of the section on injective maps picks it. Then $\mathrm{invFun}\ f\ (f\ a) = a$ by `Function.leftInverse_invFun`. In the other direction, $f(\mathrm{invFun}\ f\ b) = b$ for $b$ in the range, so the second composite is the identity on the range. $\square$

The inverse uses choice, so `Equiv.ofInjective` is noncomputable. `Equiv.ofLeftInverse'` takes an explicit left inverse and is computable. The lemmas `Equiv.ofInjective_apply` and `Equiv.apply_ofInjective_symm` give the values.

The module also proves how an equivalence acts on images and preimages: `Equiv.image_preimage`, `Equiv.preimage_image`, `Equiv.symm_image_image` and `Equiv.image_symm_image` say that $e$ and $e^{-1}$ induce inverse bijections of power sets, and `Equiv.setCongr` packages this as `Set α ≃ Set β`.

**Theorem.** For $e : \alpha \simeq \beta$ and $s \subseteq \alpha$, $e(s^c) = e(s)^c$.

*Proof.* Let $y : \beta$ and $x = e^{-1}(y)$. Then $y \in e(s^c)$ if and only if $x \notin s$, because $e$ is injective and $y = e(x)$. Also $y \in e(s)$ if and only if $x \in s$. So $y \in e(s^c)$ if and only if $y \notin e(s)$. $\square$

This is `Equiv.image_compl`. The statement fails for a function that is not bijective: a constant map on a type with two points sends $s$ and $s^c$ to the same set.

#### Embeddings and sets: `Mathlib.Logic.Embedding.Set` and `Mathlib.Logic.Equiv.Embedding`

`Function.Embedding.codRestrict` restricts the codomain of an embedding to a set that contains its range. `Set.embeddingOfSubset` is the inclusion $s \hookrightarrow t$ for $s \subseteq t$, and `Function.Embedding.image` sends an embedding $\alpha \hookrightarrow \beta$ to the embedding of power sets $s \mapsto f(s)$. Disjoint sets give embeddings of sums: `Function.Embedding.sumSet` embeds $s \oplus t$ in $\alpha$ when $s$ and $t$ are disjoint, and `Function.Embedding.sigmaSet` does the same for a pairwise disjoint family. `Function.Embedding.optionElim` extends an embedding $f$ to `Option α` by a point $x$ outside the range of $f$, and `Function.Embedding.optionEmbeddingEquiv` states that every embedding of `Option α` is of this form.

The module `Mathlib.Logic.Equiv.Embedding` describes the type of embeddings of a sum. An embedding of $\alpha \oplus \beta$ into $\gamma$ is a pair of embeddings with disjoint ranges, by `Equiv.sumEmbeddingEquivProdEmbeddingDisjoint`. It is also an embedding $f$ of $\alpha$ together with an embedding of $\beta$ into the complement of the range of $f$, by `Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted`. Finally, `Equiv.uniqueEmbeddingEquivResult` identifies the embeddings of a type with one element with the points of the codomain.

#### Functors: `Mathlib.Logic.Equiv.Functor`

A lawful functor `f : Type u → Type v` acts on equivalences: `Functor.mapEquiv f e : f α ≃ f β` acts by `e <$> ·`, and its inverse acts by `e.symm <$> ·`. The lemmas `Functor.mapEquiv_apply`, `Functor.mapEquiv_symm_apply` and `Functor.mapEquiv_refl` record this. `Bifunctor.mapEquiv` does the same for a functor of two arguments, with the value given by `Bifunctor.mapEquiv_apply`.

#### Common errors

1. A learner looks for `Equiv.prodCongr_apply` to rewrite `e.prodCongr e' (a, b)` and finds the statement `⇑(e₁.prodCongr e₂) = Prod.map ⇑e₁ ⇑e₂`. The lemma is about the function, not a point. Use `simp`, which applies it and then computes `Prod.map` on the pair.
2. A learner applies `Equiv.Set.union` or `Equiv.Set.sumCompl` and gets the error that an instance of `DecidablePred` is missing. Add `classical` at the start of the proof, or give the instance.
3. A learner expects `(Equiv.ofInjective f hf).symm ⟨f a, _⟩ = a` to hold by `rfl`. The inverse is defined by choice. Use `Equiv.ofInjective_symm_apply` or `Equiv.apply_ofInjective_symm` with injectivity.

### Exercises

1. (A) Write the equivalence `Equiv.sumComm α β` by hand, as a structure with its four fields, and prove the two inverse laws by a case split.
2. (A) Use `Equiv.prodPUnit`, `Equiv.prodComm` and `Equiv.trans` to build an equivalence $\mathrm{PUnit} \times \alpha \simeq \alpha$, and compare it with `Equiv.punitProd`.
3. (B) Construct $\mathrm{Option}\ (\alpha \oplus \beta) \simeq \mathrm{Option}\ \alpha \oplus \beta$ from the equivalences of this section, with no direct definition.
4. (B) Prove that the equivalence $\alpha \simeq \beta$ of `Equiv.removeNone e` is well defined: if $e(\mathrm{some}\ x) = \mathrm{none}$, then $e(\mathrm{none})$ is of the form $\mathrm{some}\ y$.
5. (B) For disjoint sets $s$ and $t$, prove that the composite of `Equiv.Set.union` with `Function.Embedding.sumSet` sends each point of $s \cup t$ to itself.
6. (C) Use `Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted` to prove that there are $n(n-1)\cdots(n-k+1)$ embeddings of a type with $k$ elements into a type with $n$ elements.

### Reference

<?reference?>
