---
title: The algebra structure and functoriality of adic completions
kind: api
modules:
  - Mathlib.RingTheory.AdicCompletion.Algebra
  - Mathlib.RingTheory.AdicCompletion.Functoriality
  - Mathlib.RingTheory.AdicCompletion.RingHom
  - Mathlib.RingTheory.AdicCompletion.Topology
explains:
  E2: [AdicCompletion.evalₐ, AdicCompletion.liftRingHom, AdicCompletion.kerProj, AdicCompletion.map, AdicCompletion.sumEquivOfFintype, surjective_of_mkQ_comp_surjective, IsAdicComplete.liftRingHom, IsAdicComplete.algHom_ext, IsAdic.isAdicComplete_iff]
  E1: auto
families: []
requires: [V09, V10.C02, V14]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The algebra structure and functoriality of adic completions

### Overview

The previous section defines the completion $\hat M = \varprojlim_n M/I^nM$ of a module and proves its main properties. This section describes the rest of the API in the folder `Mathlib/RingTheory/AdicCompletion/`: the ring and algebra structure on $\hat R$, the module structure of $\hat M$ over $\hat R$, the maps that a linear map induces on completions, the universal property of a complete ring, and the comparison with the completeness of a uniform space.

A reader needs these results to compute with completions. For example, to build a map $A \to \hat R$ one gives a compatible family of maps $A \to R/I^n$. To show that a map $M \to N$ is surjective onto a complete module, one checks it modulo $I$. These two facts are the main tools of the section, and both have short proofs.

### The library around it

#### The ring structure

Let $I$ be an ideal of a commutative ring $R$. The type `AdicCompletion I R` is a set of compatible families in $\prod_n R/I^nR$. The library defines the multiplication componentwise, with the instances `AdicCompletion.instMul`, `AdicCompletion.instOne` and `AdicCompletion.instCommRing`. The lemmas `AdicCompletion.val_mul` and `AdicCompletion.val_one` say that the $n$-th component of a product is the product of the components. The Cauchy sequences have the same structure, `AdicCompletion.instCommRingAdicCauchySequence`, and `AdicCompletion.mkₐ` is the algebra map from Cauchy sequences to the completion. As sets, the two rings are `AdicCompletion.subring` and `AdicCompletion.AdicCauchySequence.subring`, with the algebra versions `AdicCompletion.subalgebra` and `AdicCompletion.AdicCauchySequence.subalgebra`.

If $R$ is an $S$-algebra, then so is $\hat R$, by `AdicCompletion.instAlgebra`. The lemma `AdicCompletion.algebraMap_apply` says that $s \mapsto$ `AdicCompletion.of I R (algebraMap S R s)`, so the structure map factors through $R \to \hat R$. For a module $M$, the instance `AdicCompletion.module` makes $\hat M$ an $\hat R$-module. The scalar action is again componentwise: `AdicCompletion.smul_eval` says that $(r \cdot x)_n = r_n \cdot x_n$, where $r_n \in R/I^n$ acts on $M/I^nM$.

There is a technical point. The module completion uses the quotients $R/(I^n \cdot \top)$, where $I^n \cdot \top$ is the submodule $I^nR$ of $R$. This submodule is equal to the ideal $I^n$, but it is not definitionally equal. The library does not make a second type for rings. Instead it gives the maps to $R/I^n$ as separate definitions:

| Lean name | Statement |
|---|---|
| `AdicCompletion.evalₐ` | the algebra map $\hat R \to R/I^n$ |
| `AdicCompletion.evalOneₐ` | the algebra map $\hat R \to R/I$ |
| `AdicCompletion.surjective_evalₐ` | each map $\hat R \to R/I^n$ is surjective |
| `AdicCompletion.ext_evalₐ` | two elements with the same images in all $R/I^n$ are equal |
| `AdicCompletion.factor_eval_eq_evalₐ` | `evalₐ` agrees with the module map `AdicCompletion.eval` after the identification |
| `AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk` | $R \to \hat R \to R/I$ is the quotient map |
| `AdicCompletion.transitionMapₐ` | the algebra map $R/I^n \to R/I^m$ for $m \le n$ |
| `AdicCompletion.ofAlgEquiv` | a complete ring $S$ is isomorphic to its completion as an $S$-algebra |

#### Lifting maps into a completion

The completion is an inverse limit, and a map into an inverse limit is a compatible family of maps. Let $S$ be a ring and $A$ another ring. A family of ring maps $f_n : A \to S/I^n$ is compatible if $\pi_{m,n} \circ f_n = f_m$ for $m \le n$, where $\pi_{m,n} : S/I^n \to S/I^m$ is the projection `Ideal.Quotient.factorPow`. Then `AdicCompletion.liftRingHom I f hf : A →+* AdicCompletion I S` is the unique ring map with components $f_n$. The lemma `AdicCompletion.evalₐ_liftRingHom` says that $\mathrm{ev}_n \circ \mathrm{lift} = f_n$. The version for $R$-algebra maps is `AdicCompletion.liftAlgHom`, with the compatibility stated through `Ideal.Quotient.factorₐ`.

If $S$ is complete, then the map $S \to \hat S$ is an isomorphism, and the lift lands in $S$. The module `Mathlib.RingTheory.AdicCompletion.RingHom` gives this universal property of a complete ring.

**Proposition.** Let $S$ be $I$-adically complete and let $(f_n : A \to S/I^n)$ be a compatible family of ring maps. Then there is a unique ring map $f : A \to S$ with $f \bmod I^n = f_n$ for all $n$.

*Proof.* Compose `AdicCompletion.liftRingHom` with the inverse of the isomorphism $S \to \hat S$. Uniqueness: if $f$ and $g$ agree modulo every $I^n$, then $f(a) - g(a) \in \bigcap_n I^n = 0$, since $S$ is Hausdorff. $\square$

The construction is `IsAdicComplete.liftRingHom`. The lemma `IsAdicComplete.mk_liftRingHom` gives the components, and `IsAdicComplete.of_liftRingHom` compares the result with `AdicCompletion.liftRingHom`. The uniqueness for algebra maps is `IsAdicComplete.algHom_ext`: two $R$-algebra maps $A \to S$ that agree after each quotient map to $S/I^n$ are equal. The algebra version of the lift is `IsAdicComplete.liftAlgHom`.

A family indexed by a subsequence also gives a lift. Let $a : \mathbb{N} \to \mathbb{N}$ be strictly increasing, and let $f_n : A \to S/I^{a(n)}$ be maps with $\pi \circ f_{n+1} = f_n$. Then `IsAdicComplete.StrictMono.liftRingHom` is the lift. The lemma `IsAdicComplete.StrictMono.factorPow_comp_eq_of_factorPow_comp_succ_eq'` reduces the compatibility for all $m \le n$ to the compatibility for consecutive indices. This form is convenient for Newton's method, where the $n$-th approximation is correct modulo $I^{2^n}$.

The completion along the kernel of a surjection has a canonical projection. Let $f : S \to A$ be a surjective $R$-algebra map with kernel $J$. Then `AdicCompletion.kerProj hf` is the map $\hat S_J \to S/J \cong A$, and `AdicCompletion.kerProj_of` says that it extends $f$. The lemma `AdicCompletion.kerProj_surjective` says that it is surjective.

#### Functoriality

A linear map $f : M \to N$ maps $I^nM$ into $I^nN$, so it induces maps $M/I^nM \to N/I^nN$ that are compatible in $n$. The limit is `AdicCompletion.map I f`. The map is $\hat R$-linear, and `AdicCompletion.map` is itself $R$-linear in $f$. The usual functor laws hold: `AdicCompletion.map_id`, `AdicCompletion.map_comp` and `AdicCompletion.map_of`, which says that the square with $M \to \hat M$ and $N \to \hat N$ commutes. The Cauchy sequences have the same functor `AdicCompletion.AdicCauchySequence.map`. The map at the level $n = 1$ is `LinearMap.reduceModIdeal`, the map $M/IM \to N/IN$ as a linear map over $R/I$. A linear equivalence gives `AdicCompletion.congr`, a linear equivalence of completions.

To check that two maps out of $\hat M$ are equal, it is enough to check them on Cauchy sequences: this is `AdicCompletion.map_ext`. The variants `AdicCompletion.map_ext'` and `AdicCompletion.map_ext''` check linear maps on the image of $M$ and on the levels.

Completion commutes with finite sums and products.

| Lean name | Statement |
|---|---|
| `AdicCompletion.sum` | the map $\bigoplus_i \hat M_i \to (\bigoplus_i M_i)^\wedge$ |
| `AdicCompletion.sumInv` | the map in the other direction, for a finite index type |
| `AdicCompletion.sumEquivOfFintype` | $\bigoplus_i \hat M_i \cong (\bigoplus_i M_i)^\wedge$ for a finite index type |
| `AdicCompletion.pi` | the map $(\prod_i M_i)^\wedge \to \prod_i \hat M_i$ |
| `AdicCompletion.piEquivOfFintype` | $(\prod_i M_i)^\wedge \cong \prod_i \hat M_i$ for a finite index type |
| `AdicCompletion.piEquivFin` | $(R^n)^\wedge \cong \hat R^n$ |

The equivalence `AdicCompletion.piEquivFin` is the first step of the proof, in the previous section, that $\hat R \otimes_R M \cong \hat M$ for a finite module over a Noetherian ring.

#### Surjectivity modulo the ideal

The most useful result of `Mathlib.RingTheory.AdicCompletion.Functoriality` is a form of Nakayama's lemma for complete modules.

**Proposition.** Let $M$ be $I$-adically precomplete and $N$ be $I$-adically Hausdorff. Let $f : M \to N$ be linear, and assume that the composite $M \to N \to N/IN$ is surjective. Then $f$ is surjective.

*Proof.* First, for $y \in I^nN$ there is $x \in I^nM$ with $f(x) \equiv y \pmod{I^{n+1}N}$. Indeed, write $y = \sum_j a_jy_j$ with $a_j \in I^n$ and $y_j \in N$. By hypothesis $y_j = f(x_j) + z_j$ with $z_j \in IN$. Then $x = \sum_j a_jx_j$ works, since $\sum_j a_jz_j \in I^{n+1}N$. This is `AdicCompletion.exists_smodEq_pow_add_one_smul`.

Now let $y \in N$. Choose $x_0$ with $f(x_0) \equiv y \pmod{IN}$. Apply the first step to $y - f(x_0) \in IN$, and so on. This gives $x_0, x_1, \dots$ with $x_n \in I^nM$ and $y - f(x_0 + \dots + x_n) \in I^{n+1}N$. The partial sums form a Cauchy sequence in $M$, with a limit $x$. Then $y - f(x) \in I^{n+1}N$ for every $n$, so $y = f(x)$, because $N$ is Hausdorff. $\square$

The result is `surjective_of_mkQ_comp_surjective`. The ring version `surjective_of_mk_map_comp_surjective` says that a ring map $f : R \to S$ from a precomplete ring is surjective when $R \to S/f(I)S$ is surjective and $S$ is Hausdorff for $f(I)S$. On completions, `AdicCompletion.map_surjective_of_mkQ_comp_surjective` gives the surjectivity of $\hat f$ under the same condition modulo $I$, without any completeness of $M$ or $N$.

#### The adic topology

Volume 14 gives a ring the $I$-adic topology, in which the powers $I^n$ form a basis of neighbourhoods of $0$. The predicate `IsAdic I` says that a given topology on $R$ is the $I$-adic one. The module `Mathlib.RingTheory.AdicCompletion.Topology` compares the algebraic and the topological conditions.

| Lean name | Statement |
|---|---|
| `IsAdic.isHausdorff_iff` | `IsHausdorff I R` if and only if $R$ is a `T2Space` |
| `IsAdic.isPrecomplete_iff` | `IsPrecomplete I R` if and only if $R$ is a `CompleteSpace` |
| `IsAdic.isAdicComplete_iff` | `IsAdicComplete I R` if and only if $R$ is complete and Hausdorff |
| `IsAdicComplete.congr_ringEquiv` | completeness moves along a ring isomorphism |
| `IsHausdorff.congr_ringEquiv` | the same for the Hausdorff property |
| `IsPrecomplete.congr_ringEquiv` | the same for precompleteness |

The precomplete statements need a uniform structure that is compatible with the addition, `IsUniformAddGroup R`. The proof of `IsAdic.isHausdorff_iff` is direct: the closure of $\{0\}$ is $\bigcap_n I^n$, since the $I^n$ are a basis of neighbourhoods of $0$.

#### Common errors

1. The components of an element of `AdicCompletion I R` live in `R ⧸ I ^ n • ⊤`, not in `R ⧸ I ^ n`. Use `AdicCompletion.evalₐ` to get an element of the ring quotient, and `AdicCompletion.factor_eval_eq_evalₐ` to move between the two forms.
2. `AdicCompletion.liftRingHom` needs the compatibility for all $m \le n$. With a family that is only given for consecutive indices, use the `StrictMono` versions or prove the general compatibility by induction first.
3. `surjective_of_mkQ_comp_surjective` asks for precompleteness of the source and the Hausdorff property of the target. Without precompleteness of the source, the statement is false: $\mathbb{Z} \to \mathbb{Z}_p$ is surjective modulo $p$ but not surjective.

### Exercises

1. (A) Use `AdicCompletion.ext_evalₐ` to show that the map $\hat R \to \prod_n R/I^n$ is injective.
2. (A) Show that $\mathbb{Z}_p \to \mathbb{F}_p$, the map `AdicCompletion.evalOneₐ`, has kernel $p\mathbb{Z}_p$.
3. (B) Let $S$ be complete for $I$, and let $f_n : \mathbb{Z}[X] \to S/I^n$ send $X$ to the class of a fixed $s \in S$. Check that the family is compatible, and show that `IsAdicComplete.liftRingHom` sends $X$ to $s$.
4. (B) Show that a finite module $M$ over a complete local ring is generated by $x_1, \dots, x_k$ if their images generate $M/\mathfrak mM$, with `surjective_of_mkQ_comp_surjective` and the map $R^k \to M$.
5. (B) Prove that completion commutes with finite direct sums directly from the definition of $\hat M$.
6. (C) Show that the completion of an infinite direct sum $\bigoplus_{\mathbb{N}} R$ at $I$ need not be $\bigoplus_{\mathbb{N}} \hat R$, with $R = \mathbb{Z}$ and $I = (p)$.

### Reference

<?reference?>
