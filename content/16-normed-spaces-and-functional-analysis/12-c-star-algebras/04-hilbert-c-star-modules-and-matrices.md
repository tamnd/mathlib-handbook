---
title: Hilbert C*-modules and matrices over a C*-algebra
kind: api
modules:
  - Mathlib.Analysis.CStarAlgebra.Module.Defs
  - Mathlib.Analysis.CStarAlgebra.Module.Synonym
  - Mathlib.Analysis.CStarAlgebra.Module.Constructions
  - Mathlib.Analysis.CStarAlgebra.CStarMatrix
explains:
  E2: [CStarModule, CStarModule.norm_eq_sqrt_norm_inner_self, CStarModule.inner_mul_inner_swap_le, CStarModule.norm_inner_le, CStarModule.normedAddCommGroup, WithCStarModule, WithCStarModule.prod_inner, CStarMatrix, CStarMatrix.toCLM, CStarMatrix.instCStarAlgebra]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C02, V16.C06, V16.C09]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Hilbert C*-modules and matrices over a C*-algebra

### Overview

A Hilbert C*-module over a C*-algebra $A$ is a module $E$ with an inner product that takes values in $A$ instead of $\mathbb{C}$. The axioms copy those of an inner product space: $\langle x, y \rangle$ is additive and complex linear in $y$, $A$-linear in $y$ in the sense that $\langle x, a y \rangle = a \langle x, y \rangle$, and $\langle x, y \rangle^* = \langle y, x \rangle$. Positivity means that $\langle x, x \rangle \ge 0$ in the order of $A$ from Section 3, and that $\langle x, x \rangle = 0$ only for $x = 0$. The norm is $\|x\| = \|\langle x, x \rangle\|^{1/2}$, with the norm of $A$ on the right.

With $A = \mathbb{C}$, a Hilbert C*-module is a complex inner product space. With $E = A$, the algebra is a module over itself with $\langle x, y \rangle = y x^*$ in the convention above, and the norm is $\|y y^*\|^{1/2} = \|y\|$ by the C*-identity. The finite sums $E \oplus F$ and $A^n$ are modules with the inner product $\langle (x_1, x_2), (y_1, y_2) \rangle = \langle x_1, y_1 \rangle + \langle x_2, y_2 \rangle$.

The main inequality is a Cauchy Schwarz inequality in $A$: $\langle x, y \rangle \langle y, x \rangle \le \|x\|^2 \langle y, y \rangle$. Taking norms gives $\|\langle x, y \rangle\| \le \|x\| \|y\|$. The proof copies the scalar proof with care about the order of products. For $x \ne 0$, set $a = \langle x, y \rangle$ and expand the positive element $\langle y - t a^* x', y - t a^* x' \rangle$ with a suitable scalar $t$ and $x' = x / \|x\|$. The positivity of this element and the bound $\langle x', x' \rangle \le 1$ give the inequality. From Cauchy Schwarz, the triangle inequality $\|x + y\| \le \|x\| + \|y\|$ follows as in Chapter 6, so $\|\cdot\|$ is a norm.

The Riesz theorem fails for Hilbert C*-modules: a bounded $A$-linear functional need not be of the form $\langle x, \cdot \rangle$, and a closed submodule need not have a complement. But the module $A^n$ gives a C*-algebra of operators. An $n \times n$ matrix $M$ with entries in $A$ acts on $A^n$ by matrix multiplication, and the operator norm makes the matrices $M_n(A)$ a C*-algebra. This algebra is the domain of the completely positive maps of Section 5.

### The library around it

The file `Mathlib.Analysis.CStarAlgebra.Module.Defs` defines the class `CStarModule A E`. It is stated with very weak assumptions on `A`: a star ring with an action of `ℂ`, a partial order and a norm, so the class makes sense before the order on a C*-algebra is in place. The inner product is `inner A x y`, with the notation `⟪x, y⟫_A`. The fields are `CStarModule.inner_add_right`, `CStarModule.inner_self_nonneg`, `CStarModule.inner_self`, `CStarModule.inner_op_smul_right` for $\langle x, a y \rangle = a \langle x, y \rangle$, `CStarModule.inner_smul_right_complex`, `CStarModule.star_inner` and `CStarModule.norm_eq_sqrt_norm_inner_self`. The norm is part of the data of `E`, and the last field relates it to the inner product. This design lets a type keep its own norm when it agrees with the module norm.

The derived algebra lemmas are `CStarModule.inner_add_left`, `CStarModule.inner_sub_left`, `CStarModule.inner_neg_left`, `CStarModule.inner_sum_left` and their right forms, `CStarModule.inner_smul_left_complex`, `CStarModule.inner_zero_left` and `CStarModule.isSelfAdjoint_inner_self`. The inner product as a bundled map is `CStarModule.innerₛₗ`, conjugate linear in the first argument and linear in the second.

The analytic lemmas need `StarOrderedRing A` and a C*-algebra. The Cauchy Schwarz inequality is `CStarModule.inner_mul_inner_swap_le`, in the order of `A`, and `CStarModule.norm_inner_le` is its norm form. Then `CStarModule.norm_triangle`, `CStarModule.norm_zero_iff`, `CStarModule.norm_nonneg` and `CStarModule.norm_pos` are the norm axioms, collected in `CStarModule.normedSpaceCore`. The definition `CStarModule.normedAddCommGroup` builds the normed group structure from them. It is not an instance, because a type often has a topology and a uniformity already, and the instance would give a second one. The lemma `CStarModule.norm_eq_csSup` writes the norm as the supremum of $\|\langle w, v \rangle\|$ over $\|w\| \le 1$, as for a Hilbert space. With this structure, `CStarModule.continuous_inner` and the continuous form `CStarModule.innerSL` follow.

The file `Mathlib.Analysis.CStarAlgebra.Module.Synonym` defines the type synonym `WithCStarModule A E`, with the notation `C⋆ᵐᵒᵈ(A, E)`. It is needed for products. The type `E × F` already has the supremum norm, and the module norm is a different one, so the module instance goes on the synonym. The equivalence `WithCStarModule.equiv` maps the synonym back to `E`, and `WithCStarModule.linearEquiv` and `WithCStarModule.equivL` are its linear and continuous linear forms. The synonym copies the algebra, the uniformity and the bornology of `E`, by `WithCStarModule.instAddCommGroup`, `WithCStarModule.instUniformSpace` and `WithCStarModule.instBornology`, so the topology does not change.

The file `Mathlib.Analysis.CStarAlgebra.Module.Constructions` gives four examples. The instance `WithCStarModule.instCStarModule` makes `A` a module over itself with the inner product $y x^*$. The instances `WithCStarModule.instCStarModuleProd` and `WithCStarModule.instCStarModuleForall` treat finite products on the synonym, with `WithCStarModule.prod_inner` and `WithCStarModule.pi_inner` for the inner product and `WithCStarModule.prod_norm` and `WithCStarModule.pi_norm` for the norm. The norm comparisons `WithCStarModule.max_le_prod_norm`, `WithCStarModule.prod_norm_le_norm_add`, `WithCStarModule.norm_apply_le_norm` and `WithCStarModule.pi_norm_le_sum_norm` show that the module norm is equivalent to the supremum norm, so the uniformity of the synonym is the right one. The instance `WithCStarModule.instCStarModuleComplex` makes a complex inner product space a module over `ℂ`. For `A = ℂ` acting on `ℂ`, the file checks that the two possible structures agree by definition.

The file `Mathlib.Analysis.CStarAlgebra.CStarMatrix` defines `CStarMatrix m n A`, a type copy of `Matrix m n A`. The map `CStarMatrix.toCLM` sends a matrix to the continuous linear map from `C⋆ᵐᵒᵈ(A, m → A)` to `C⋆ᵐᵒᵈ(A, n → A)` given by multiplication, and `CStarMatrix.toCLM_injective` says that it is injective. The norm `CStarMatrix.instNormedAddCommGroup` is the operator norm of this map. The basic bounds are `CStarMatrix.norm_entry_le_norm` and `CStarMatrix.norm_le_of_forall_inner_le`, and `CStarMatrix.mul_entry_mul_eq_inner_toCLM` recovers an entry from the inner product. The instances `CStarMatrix.instNormedRing`, `CStarMatrix.instStarRing`, `CStarMatrix.instCStarAlgebra` and `CStarMatrix.instStarOrderedRing` make square matrices a C*-algebra with its order. The star is the conjugate transpose, by `CStarMatrix.star_eq_conjTranspose`. The algebra maps are `CStarMatrix.ofMatrixStarAlgEquiv`, `CStarMatrix.reindexₐ` for a change of index, `CStarMatrix.mapₙₐ` for entrywise application of a star homomorphism, and `CStarMatrix.toOneByOne`, which identifies $A$ with the $1 \times 1$ matrices.

The proof of the C*-identity for `CStarMatrix` goes through the module. For $v$ in $A^n$, $\langle M v, M v \rangle = \langle v, M^* M v \rangle$, so $\|M v\|^2 \le \|M^* M\| \|v\|^2$ by Cauchy Schwarz. Taking the supremum over $\|v\| \le 1$ gives $\|M\|^2 \le \|M^* M\|$, which is the field of `CStarRing`.

#### Common errors

1. A lemma on the norm of a C*-module does not apply to `E × F` with its usual norm. Move to `C⋆ᵐᵒᵈ(A, E × F)` with `WithCStarModule.equiv`.
2. `CStarModule.normedAddCommGroup` is a definition, not an instance. Use it as a local instance only when `E` has no topology of its own, or the two topologies are not the same term and lemmas fail to apply.
3. The inner product is linear in the second argument and conjugate linear in the first, as in Mathlib inner product spaces. The scalar from `A` comes out on the left: $\langle x, a y \rangle = a \langle x, y \rangle$, not $\langle x, y \rangle a$.

### Exercises

1. (A) Prove that $\langle x, x \rangle$ is self-adjoint in a C*-module with `CStarModule.star_inner`.
2. (A) Show that the norm of `A` as a module over itself is the norm of `A`, with the C*-identity.
3. (B) Prove the bound $\max(\|x\|, \|y\|) \le \|(x, y)\| \le \|x\| + \|y\|$ in `C⋆ᵐᵒᵈ(A, E × F)`.
4. (B) Derive `CStarModule.norm_inner_le` from `CStarModule.inner_mul_inner_swap_le` and the monotonicity of the norm on positive elements.
5. (B) Prove that each entry of a matrix in `CStarMatrix n n A` has norm at most the norm of the matrix, with `CStarMatrix.norm_entry_le_norm`, and deduce that the map to entries is continuous.
6. (C) Prove that for a projection $p$ in $A$, the set $\{x p : x \in A\}$ is a closed submodule of $A$, and compute its inner product.

### Reference

<?reference?>
