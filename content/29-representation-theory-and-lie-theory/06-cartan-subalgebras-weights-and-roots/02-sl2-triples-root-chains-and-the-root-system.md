---
title: sl2 triples, root chains and the root system
kind: theory
modules:
  - Mathlib.Algebra.Lie.Sl2
  - Mathlib.Algebra.Lie.Weights.Chain
  - Mathlib.Algebra.Lie.Weights.Killing
  - Mathlib.Algebra.Lie.Weights.RootSystem
  - Mathlib.Algebra.Lie.Weights.IsSimple
explains:
  E3: [IsSl2Triple, IsSl2Triple.HasPrimitiveVectorWith, IsSl2Triple.HasPrimitiveVectorWith.exists_nat, LieModule.exists_forall_mem_corootSpace_smul_add_eq_zero, LieModule.chainTopCoeff, LieAlgebra.killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero, LieAlgebra.IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg, LieAlgebra.IsKilling.coroot, LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero, LieAlgebra.IsKilling.finrank_rootSpace_eq_one, LieAlgebra.IsKilling.apply_coroot_eq_cast, LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff, LieAlgebra.IsKilling.rootSystem, LieAlgebra.IsKilling.isSimple_iff_isIrreducible]
  E2: [IsSl2Triple.lie_e_f, IsSl2Triple.lie_h_f_nsmul, IsSl2Triple.symm, IsSl2Triple.HasPrimitiveVectorWith.lie_h_pow_toEnd_f, IsSl2Triple.HasPrimitiveVectorWith.lie_e_pow_succ_toEnd_f, LieModule.chainBotCoeff, LieModule.genWeightSpaceChain, LieModule.trace_toEnd_genWeightSpaceChain_eq_zero, LieAlgebra.IsKilling.instIsLieAbelianOfIsCartanSubalgebra, LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra, LieAlgebra.IsKilling.traceForm_cartan_nondegenerate, LieAlgebra.IsKilling.cartanEquivDual, LieAlgebra.IsKilling.root_apply_coroot, IsSl2Triple.h_eq_coroot, LieAlgebra.IsKilling.span_weight_eq_top, LieSubalgebra.root, LieAlgebra.IsKilling.rootSpace_two_smul, LieAlgebra.IsKilling.rootSystem_pairing_apply, LieAlgebra.IsKilling.lieIdealOrderIso, LieAlgebra.instIsIrreducibleRootSystem_of_isSimple, LieIdeal.rootSet]
  E1: auto
families: []
requires: [V07.C06, V08.C05, V29.C04, V29.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## sl2 triples, root chains and the root system

### Overview

Section 1 split a Lie algebra $L$ into root spaces $L_\alpha$ for a Cartan subalgebra $H$. When the Killing form $\kappa$ of $L$ is nondegenerate (the Killing algebras of Chapter 5, which in characteristic $0$ are the semisimple ones), the roots have a rigid geometry. Each nonzero root $\alpha$ comes with a copy of $\mathfrak{sl}_2$ spanned by $e \in L_\alpha$, $f \in L_{-\alpha}$ and the coroot $h_\alpha = [e, f] \in H$. The representation theory of $\mathfrak{sl}_2$ then forces the numbers $\beta(h_\alpha)$ to be integers, the root spaces to be lines, and the $\alpha$-chain through $\beta$ to have no gaps.

So the roots form a reduced crystallographic root system in $H^*$, in the sense of Chapter 7, and it is irreducible if and only if $L$ is simple. Throughout, $K$ is a field of characteristic $0$, $L$ is finite dimensional with nondegenerate Killing form, and $H$ is a splitting Cartan subalgebra: a Cartan subalgebra such that $L$ is a triangularizable $H$-module. Over $\mathbb{C}$ every Cartan subalgebra splits.

### Definitions

**Definition (sl2 triple).** Elements $h, e, f$ of a Lie algebra form an *$\mathfrak{sl}_2$ triple* if $h \neq 0$, $[e, f] = h$, $[h, e] = 2e$ and $[h, f] = -2f$. Then $(-h, f, e)$ is also an $\mathfrak{sl}_2$ triple.

**Definition (Primitive vector).** For an $\mathfrak{sl}_2$ triple acting on a module $M$, a vector $m$ is *primitive* of weight $\mu$ if $m \neq 0$, $[h, m] = \mu m$ and $[e, m] = 0$.

**Definition (Root chain).** Let $\alpha \neq 0$ and $\beta$ be weights of an $H$-module $M$. The *top coefficient* $q$ is the largest $n$ such that $\beta + i\alpha$ is a weight for $0 \leq i \leq n$, and the *bottom coefficient* $r$ is the same with $-\alpha$. The *$\alpha$-chain through $\beta$* is the sum of the $M_{\beta + k\alpha}$ for $-r \leq k \leq q$.

**Definition (Coroot).** Since $\kappa$ restricted to $H$ is nondegenerate (proved below), each $\alpha \in H^*$ has a unique $t_\alpha \in H$ with $\kappa(t_\alpha, h) = \alpha(h)$ for all $h$. For a nonzero root $\alpha$, the *coroot* is $h_\alpha = 2 t_\alpha / \alpha(t_\alpha)$, so $\alpha(h_\alpha) = 2$.

### Theorems and proofs

**Lemma (The f-string).** Let $m$ be primitive of weight $\mu$ and $\psi_n = f^n m$. Then $[h, \psi_n] = (\mu - 2n)\psi_n$ and $[e, \psi_{n+1}] = (n+1)(\mu - n)\psi_n$.

*Proof.* Step 1: $[h, f x] = f[h, x] + [[h, f], x] = f[h, x] - 2 f x$, so induction on $n$ gives the first formula. Step 2: for $n = 0$, $[e, f m] = f[e, m] + [[e, f], m] = 0 + h m = \mu m$. Step 3: if the formula holds for $n - 1$, then $[e, \psi_{n+1}] = f[e, \psi_n] + h \psi_n = n(\mu - n + 1)\psi_n + (\mu - 2n)\psi_n = (n+1)(\mu - n)\psi_n$. $\square$

**Theorem (Integrality of primitive weights).** Let $R$ be a domain of characteristic $0$ and $M$ a Noetherian torsion free module. If $m$ is primitive of weight $\mu$, then $\mu = n$ for some $n \in \mathbb{N}$, $\psi_i \neq 0$ for $i \leq n$ and $\psi_{n+1} = 0$.

*Proof.* Step 1: the nonzero $\psi_i$ are eigenvectors of $h$ for the eigenvalues $\mu - 2i$, which are distinct in characteristic $0$. Eigenvectors for distinct eigenvalues are independent, and a Noetherian torsion free module has no infinite independent family. So some $\psi_i$ vanishes. Step 2: let $n + 1$ be the least index with $\psi_{n+1} = 0$, so $\psi_n \neq 0$. Step 3: the lemma gives $0 = [e, \psi_{n+1}] = (n+1)(\mu - n)\psi_n$. Since $R$ is a domain of characteristic $0$ and $M$ is torsion free, $\mu = n$. $\square$

**Theorem (Trace on a root chain).** Let $H$ be a Cartan subalgebra of $L$, $\alpha \neq 0$, and $\chi$ a weight of an $L$-module $M$, with the finiteness hypotheses of Mathlib (Noetherian modules over a principal ideal domain of characteristic $0$). There are $a \in R$ and $b > 0$ in $\mathbb{N}$ with $(a\alpha + b\chi)(x) = 0$ for all $x$ in the coroot space $[L_\alpha, L_{-\alpha}] \subseteq H$.

*Proof.* Step 1: $M$ has finitely many weights, so there are $p < 0 < q'$ with $M_{\chi + p\alpha} = M_{\chi + q'\alpha} = 0$. Let $C = \bigoplus_{p < k < q'} M_{\chi + k\alpha}$. Step 2: for $y \in L_\alpha$ and $z \in L_{-\alpha}$, Section 1 gives $[y, M_{\chi + k\alpha}] \subseteq M_{\chi + (k+1)\alpha}$ and $[z, M_{\chi + k\alpha}] \subseteq M_{\chi + (k-1)\alpha}$. The end spaces are $0$, so $C$ is stable under $y$ and $z$. Step 3: so $\rho([y, z])$ on $C$ is the commutator of $\rho(y)|_C$ and $\rho(z)|_C$, and its trace is $0$. By linearity this holds for all $x$ in the coroot space. Step 4: by the trace formula of Section 1, $0 = \sum_k d_k (\chi + k\alpha)(x)$ with $d_k = \operatorname{rank} M_{\chi + k\alpha}$. Put $a = \sum_k k d_k$ and $b = \sum_k d_k$, which is positive since $d_0 > 0$. $\square$

From now on $L$ is a Killing algebra over $K$ and $H$ a splitting Cartan subalgebra.

**Proposition (Orthogonality of root spaces).** If $x \in L_\alpha$, $y \in L_\beta$ and $\alpha + \beta \neq 0$, then $\kappa(x, y) = 0$. The form $\kappa$ restricted to $H$ is nondegenerate.

*Proof.* Step 1: by Section 1, $\operatorname{ad} x \operatorname{ad} y$ maps $L_\gamma$ into $L_{\gamma + \alpha + \beta}$. The weights are finite in number and $\alpha + \beta \neq 0$, so a power of this map sends every $L_\gamma$ to $0$. A nilpotent map has trace $0$. Step 2: $L = H \oplus \bigoplus_{\alpha \neq 0} L_\alpha$ and $H = L_0$. By Step 1 with $\beta = 0$, $\kappa(H, L_\alpha) = 0$ for $\alpha \neq 0$. An $h \in H$ orthogonal to $H$ is then orthogonal to $L$, and $h = 0$ since $\kappa$ is nondegenerate. $\square$

Mathlib also proves that $H$ is abelian and that each $\operatorname{ad} h$ with $h \in H$ is semisimple, so $[h, x] = \alpha(h) x$ for $x \in L_\alpha$. The text uses these facts without proof.

**Proposition (Bracket of opposite root spaces).** For $e \in L_\alpha$ and $f \in L_{-\alpha}$, $[e, f] = \kappa(e, f)\, t_\alpha$.

*Proof.* Both sides lie in $H = L_0$. For $h \in H$, invariance of $\kappa$ gives $\kappa(h, [e, f]) = \kappa([h, e], f) = \alpha(h)\kappa(e, f) = \kappa(h, \kappa(e, f) t_\alpha)$. Nondegeneracy on $H$ gives the equality. $\square$

**Theorem (sl2 triples for roots).** Let $\alpha \neq 0$ be a root. Then $\alpha(t_\alpha) \neq 0$, and there are $e \in L_\alpha$ and $f \in L_{-\alpha}$ such that $(h_\alpha, e, f)$ is an $\mathfrak{sl}_2$ triple.

*Proof.* Step 1: $\kappa$ pairs $L_\alpha$ with $L_{-\alpha}$, by orthogonality and nondegeneracy, so there are $e, f$ with $\kappa(e, f) = 1$, and $[e, f] = t_\alpha \neq 0$. So the coroot space is $K t_\alpha$. Step 2: suppose $\alpha(t_\alpha) = 0$. For each root $\chi$, the chain theorem gives $b > 0$ with $(a\alpha + b\chi)(t_\alpha) = 0$, so $\chi(t_\alpha) = 0$. Then $\operatorname{ad} t_\alpha$ has only the eigenvalue $0$ and is nilpotent. It is also semisimple, so $\operatorname{ad} t_\alpha = 0$. The center of a Killing algebra is $0$, so $t_\alpha = 0$, a contradiction. Step 3: rescale $f$ so that $\kappa(e, f) = 2 / \alpha(t_\alpha)$. Then $[e, f] = h_\alpha$, $[h_\alpha, e] = \alpha(h_\alpha) e = 2e$ and $[h_\alpha, f] = -2f$. $\square$

**Theorem (Root spaces are lines).** For a nonzero root $\alpha$, $\dim L_\alpha = 1$.

*Proof.* Take the triple $(h_\alpha, e, f)$ of the theorem. Suppose $\dim L_{-\alpha} \geq 2$. Step 1: the map $y \mapsto \kappa(e, y)$ on $L_{-\alpha}$ has a nonzero kernel, so there is $y \neq 0$ in $L_{-\alpha}$ with $\kappa(e, y) = 0$. Step 2: then $[e, y] = 0$ by the bracket proposition, and $[h_\alpha, y] = -\alpha(h_\alpha) y = -2y$. So $y$ is primitive of weight $-2$ in the module $L$. Step 3: integrality says $-2 \in \mathbb{N}$, a contradiction. So $\dim L_{-\alpha} = 1$ for every nonzero root, and the same holds with $-\alpha$ in place of $\alpha$. $\square$

**Theorem (Root chains).** Let $\alpha \neq 0$ and $\beta$ be roots with top and bottom coefficients $q$ and $r$. Then $\beta(h_\alpha) = r - q$, and for $n \in \mathbb{Z}$, $\beta + n\alpha$ is a root or zero exactly when $-r \leq n \leq q$.

*Proof.* Step 1: $L_{\beta + q\alpha} \neq 0$ and $L_{\beta + (q+1)\alpha} = 0$, so $e$ kills any nonzero $v \in L_{\beta + q\alpha}$. So $v$ is primitive of weight $\mu = \beta(h_\alpha) + 2q$. By integrality, $f^i v \neq 0$ for $i \leq \mu$, and $f^i v \in L_{\beta + (q - i)\alpha}$. So $\beta + j\alpha$ is a weight for $-q - \beta(h_\alpha) \leq j \leq q$. Since $\beta - (r+1)\alpha$ is not a weight, $-q - \beta(h_\alpha) \geq -r$, that is, $\beta(h_\alpha) \leq r - q$. Step 2: the same argument for the triple $(-h_\alpha, f, e)$ and the bottom of the chain gives $-\beta(h_\alpha) \leq q - r$. So $\beta(h_\alpha) = r - q$. Step 3: if $\beta + n\alpha$ were a weight for some $n \geq q + 2$, apply Step 1 and 2 to $\beta' = \beta + n\alpha$ with $n$ least. Its bottom coefficient is $0$, so $\beta'(h_\alpha) = -q' \leq 0$. But $\beta'(h_\alpha) = r - q + 2n > 0$. The case $n \leq -r - 2$ is symmetric. $\square$

**Corollary (Reflections and reducedness).** For roots $\alpha \neq 0$ and $\beta$, $\beta(h_\alpha) \in \mathbb{Z}$ and $\beta - \beta(h_\alpha)\alpha$ is a root. The multiple $2\alpha$ is not a root.

*Proof.* Step 1: $\beta(h_\alpha) = r - q$, and $n = q - r$ satisfies $-r \leq n \leq q$, so $\beta + (q - r)\alpha$ is a root by the chain theorem. Step 2: suppose $L_{2\alpha} \neq 0$ and let $k \geq 2$ be largest with $L_{k\alpha} \neq 0$. A nonzero $v \in L_{k\alpha}$ is primitive of weight $2k$, so $f^{k-1} v \neq 0$ lies in $L_\alpha = K e$. Then $[e, f^{k-1} v] = 0$, but the f-string lemma gives $[e, f^{k-1} v] = (k-1)(k+2) f^{k-2} v \neq 0$. $\square$

**Theorem (The root system of a Killing algebra).** The set $\Phi$ of nonzero roots, with the coroots $h_\alpha$ and the pairing $\langle \beta, h_\alpha \rangle = \beta(h_\alpha)$, is a reduced crystallographic root system: $\Phi$ spans $H^*$, the coroots span $H$, and each reflection $s_\alpha(\beta) = \beta - \beta(h_\alpha)\alpha$ maps $\Phi$ to $\Phi$.

*Proof.* Step 1: the corollary gives integrality, reflections and reducedness. Step 2: if $\Phi$ lies in a proper subspace of $H^*$, there is $h \neq 0$ with $\alpha(h) = 0$ for all roots. Then $\operatorname{ad} h$ is nilpotent and semisimple, so $h$ is central and $h = 0$, a contradiction. Step 3: under the isomorphism $\alpha \mapsto t_\alpha$ of $H^*$ with $H$, the coroots are nonzero multiples of the images of the roots, so they span $H$. $\square$

**Theorem (Simple algebras and irreducible root systems).** The root system of $L$ is irreducible if and only if $L$ is simple.

*Proof.* Step 1: let $V \subseteq H^*$ be invariant under all reflections, $\alpha \in \Phi \cap V$ and $\beta \in \Phi \setminus V$. Then $s_\beta(\alpha) = \alpha - \alpha(h_\beta)\beta \in V$ forces $\alpha(h_\beta) = 0$, hence $\beta(h_\alpha) = 0$, since both are multiples of $\kappa(t_\alpha, t_\beta)$. If $\alpha + \beta$ were a root, it would lie outside $V$, and the same argument would give $(\alpha + \beta)(h_\alpha) = 0$, while it equals $2$. So $[L_\alpha, L_\beta] = 0$. Step 2: let $L$ be simple and $V$ such a subspace, $V \neq 0, H^*$. Let $I$ be the span of the $L_\alpha$ and the $h_\alpha$ for $\alpha \in \Phi \cap V$. By Step 1, the bracket rules of Section 1 and $[L_\alpha, L_{-\alpha}] = K h_\alpha$, $I$ is an ideal. It is nonzero, and it is not $L$ because $\Phi$ spans $H^*$. This contradicts simplicity. Step 3: let the root system be irreducible and $I \neq 0, L$ an ideal. Since $I$ is $H$-stable and root spaces are lines, $I = (I \cap H) \oplus \bigoplus_{L_\alpha \subseteq I} L_\alpha$. Let $V$ be the span of the $\alpha$ with $L_\alpha \subseteq I$. A power of $e_\beta$ or $f_\beta$ maps $L_\alpha$ onto $L_{s_\beta(\alpha)}$ by the theory of $\mathfrak{sl}_2$ strings, so $V$ is invariant. If $V = 0$, then $[I, L_\alpha] \subseteq I \cap L_\alpha = 0$ gives $\alpha(I \cap H) = 0$ for all $\alpha$, so $I = 0$. If $V = H^*$, then $I$ contains every $L_\alpha$ and every $h_\alpha$, so $I = L$. Both are excluded. $\square$

### Examples

**Example (The natural module of sl2).** Take $h = \operatorname{diag}(1, -1)$, $e = E_{12}$, $f = E_{21}$ acting on $K^2$. The vector $e_1$ is primitive of weight $1$: $h e_1 = e_1$ and $e e_1 = 0$. Then $\psi_1 = f e_1 = e_2$ and $\psi_2 = f e_2 = 0$, so $n = 1$. The lemma gives $[e, \psi_1] = 1 \cdot (1 - 0)\psi_0$, and indeed $e e_2 = e_1$. The Killing form of $\mathfrak{sl}_2$ has $\kappa(h, h) = 4 + 0 + 4 = 8$. With $\alpha(h) = 2$, $t_\alpha = h / 4$, $\alpha(t_\alpha) = 1/2$ and $h_\alpha = 4 t_\alpha = h$.

**Example (The roots of sl3).** Let $L = \mathfrak{sl}_3(\mathbb{C})$ and $H$ the diagonal matrices of trace $0$. Let $\varepsilon_i(\operatorname{diag}(t_1, t_2, t_3)) = t_i$. Since $[\operatorname{diag}(t), E_{ij}] = (t_i - t_j) E_{ij}$, the nonzero roots are the six forms $\varepsilon_i - \varepsilon_j$ with $i \neq j$, and $L_{\varepsilon_i - \varepsilon_j} = \mathbb{C} E_{ij}$. For $\alpha_1 = \varepsilon_1 - \varepsilon_2$, the triple is $(E_{11} - E_{22}, E_{12}, E_{21})$, so $h_{\alpha_1} = \operatorname{diag}(1, -1, 0)$. For $\alpha_2 = \varepsilon_2 - \varepsilon_3$, $\alpha_2(h_{\alpha_1}) = -1$. The $\alpha_1$-chain through $\alpha_2$ is $\alpha_2, \alpha_1 + \alpha_2$: $\alpha_2 - \alpha_1$ and $\alpha_2 + 2\alpha_1$ are not roots, so $r = 0$, $q = 1$ and $r - q = -1$, as the chain theorem predicts. The reflection $s_{\alpha_1}$ sends $\alpha_2$ to $\alpha_1 + \alpha_2 = \varepsilon_1 - \varepsilon_3$. This is the root system $A_2$, with six roots at angles of $60$ degrees.

**Counterexample (Without the Killing hypothesis).** In the algebra $[x, y] = y$, $H = K x$ is a Cartan subalgebra with the roots $0$ and $\alpha(x) = 1$, but $-\alpha$ is not a root and there is no $\mathfrak{sl}_2$ triple. Here $\kappa(y, \cdot) = 0$.

### The library around it

::: mathlib
`IsSl2Triple.HasPrimitiveVectorWith.exists_nat` · `Mathlib.Algebra.Lie.Sl2`

`IsSl2Triple h e f` has the fields `h_ne_zero`, `lie_e_f`, `lie_h_e_nsmul` and `lie_h_f_nsmul`, and `symm` gives `(-h, f, e)`. `HasPrimitiveVectorWith t m μ` is a primitive vector. The lemma of the text is `lie_h_pow_toEnd_f` and `lie_e_pow_succ_toEnd_f`, and the integrality theorem is `exists_nat`, with `pow_toEnd_f_ne_zero_of_eq_nat` and `pow_toEnd_f_eq_zero_of_eq_nat` for the length of the string.

<?decl IsSl2Triple.HasPrimitiveVectorWith.exists_nat?>
:::

::: mathlib
`LieModule.exists_forall_mem_corootSpace_smul_add_eq_zero` · `Mathlib.Algebra.Lie.Weights.Chain`

This is the trace theorem on a chain. `genWeightSpaceChain M α χ p q` is the sum of the spaces of the chain, and `trace_toEnd_genWeightSpaceChain_eq_zero` is Step 3. `chainTopCoeff α β` and `chainBotCoeff α β` are the coefficients $q$ and $r$, defined with `Nat.find` on the first missing weight.

<?decl LieModule.exists_forall_mem_corootSpace_smul_add_eq_zero?>
:::

::: mathlib
`LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero` · `Mathlib.Algebra.Lie.Weights.Killing`

`LieAlgebra.killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero` is orthogonality, `traceForm_cartan_nondegenerate` the nondegeneracy on `H`, and `instIsLieAbelianOfIsCartanSubalgebra` and `isSemisimple_ad_of_mem_isCartanSubalgebra` the two facts used without proof. `cartanEquivDual H : H ≃ₗ[K] Dual K H` is $h \mapsto \kappa(h, \cdot)$, so $t_\alpha$ is `(cartanEquivDual H).symm α`. `lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg` is the bracket proposition. `coroot α : H` is $h_\alpha$ and `IsSl2Triple.h_eq_coroot` says that every triple for $\alpha$ has $h = h_\alpha$. `finrank_rootSpace_eq_one` is the theorem on lines, and `span_weight_eq_top` is Step 2 of the root system theorem.

<?decl LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero?>
:::

::: mathlib
`LieAlgebra.IsKilling.rootSystem` · `Mathlib.Algebra.Lie.Weights.RootSystem`

`rootSystem H : RootPairing H.root K (Dual K H) H` is indexed by the nonzero roots, with roots in $H^*$ and coroots in $H$. Instances record that it is a root system, crystallographic and reduced. `rootSystem_pairing_apply` states that the pairing of `β` and `α` is `β (coroot α)`. `apply_coroot_eq_cast` is $\beta(h_\alpha) = r - q$, `rootSpace_zsmul_add_ne_bot_iff` is the chain theorem and `rootSpace_two_smul` is reducedness. `corootForm_rootSystem_eq_killing` identifies the canonical form of Chapter 7 with $\kappa$ on $H$.

<?decl LieAlgebra.IsKilling.rootSystem?>
:::

::: mathlib
`LieAlgebra.IsKilling.isSimple_iff_isIrreducible` · `Mathlib.Algebra.Lie.Weights.IsSimple`

The proof goes through `lieIdealOrderIso H : LieIdeal K L ≃o (rootSystem H).invtRootSubmodule`, the order isomorphism of the text. `LieIdeal.rootSet` and `` are Step 1, and `invtSubmoduleToLieIdeal` is Step 2. The instance `LieAlgebra.instIsIrreducibleRootSystem_of_isSimple` gives the irreducibility for a simple `L`.

<?decl LieAlgebra.IsKilling.isSimple_iff_isIrreducible?>
:::

Common errors of a learner: The first error is to look for a type of roots in `H →ₗ[K] K`; Mathlib's roots are `Weight K H L`, functions that are linear by an instance, and the root system is indexed by the subtype `H.root`. The second error is to use `IsSemisimple` where the files ask `IsKilling`; in characteristic $0$ the two agree, but the instance must be found. The third error is to forget `[IsTriangularizable K H L]`: over $\mathbb{R}$ the algebra $\mathfrak{so}_3$ has a Cartan subalgebra without real roots. The fourth error is to read `lie_h_f_nsmul` as `⁅h, f⁆ = -2 • f`; it is `-(2 • f)`, with a natural number scalar.

### Exercises

1. (A) Check that $(\operatorname{diag}(1, -1, 0), E_{12}, E_{21})$ is an $\mathfrak{sl}_2$ triple in $\mathfrak{sl}_3$. Hint: compute three brackets of matrices.
2. (A) Find the weights of the adjoint module of $\mathfrak{sl}_2$ for the triple $(h, e, f)$ and the primitive vector. Hint: $e$ is primitive of weight $2$.
3. (A) In $\mathfrak{sl}_3$, list the $\alpha_1$-chain through each of the six roots and check that $\beta(h_{\alpha_1}) = r - q$. Hint: $\beta(h_{\alpha_1}) = \beta_1 - \beta_2$ for $\beta = \sum \beta_i \varepsilon_i$.
4. (B) Show that the Killing form of $\mathfrak{sl}_3$ is $\kappa(x, y) = 6 \operatorname{tr}(xy)$ and find $t_{\alpha_1}$. Hint: compute $\kappa(h, h)$ for one diagonal $h$ and use invariance; the answer is $t_{\alpha_1} = \operatorname{diag}(1, -1, 0)/6$.
5. (B) Prove that if $\alpha$ is a root, then $c\alpha$ is a root only for $c = \pm 1$. Hint: use the corollary for $\alpha$ and for $c\alpha$, and note $\alpha(h_{c\alpha}) = 2/c$.
6. (B) Show that in a Killing algebra, $[L_\alpha, L_\beta] = L_{\alpha + \beta}$ when $\alpha$, $\beta$ and $\alpha + \beta$ are nonzero roots. Hint: use the f-string lemma on the $\alpha$-chain through $\beta$.
7. (C) Let $\mathfrak{so}_5(\mathbb{C})$ preserve $x_1 x_2 + x_3 x_4 + x_5^2$ on $\mathbb{C}^5$. Show that its root system is $B_2$, with $8$ roots. Hint: $H = \{\operatorname{diag}(a, -a, b, -b, 0)\}$, and the roots are $\pm \varepsilon_1 \pm \varepsilon_2$ and $\pm \varepsilon_1$, $\pm \varepsilon_2$.

### Notes and history

Killing classified the simple Lie algebras over $\mathbb{C}$ through their roots, and Cartan completed the work in his thesis of 1894. The method of $\mathfrak{sl}_2$ triples and root chains is the modern form of their argument, as in the books of Jacobson, Serre and Humphreys. Serre's notes on complex semisimple Lie algebras of 1966 present the passage from a Lie algebra to its root system and back.

The Mathlib files are by these authors, read from their headers: `Sl2`, `Weights.Chain` and `Weights.Killing` by Oliver Nash; `Weights.RootSystem` by Andrew Yang; `Weights.IsSimple` by Janos Wolosz.

### Reference

<?reference?>
