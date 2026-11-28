---
title: The complex numbers
kind: api
modules:
  - Mathlib.Basic.Complex.Basic
  - Mathlib.Basic.Complex.BigOperators
  - Mathlib.Data.Complex.Basic
  - Mathlib.Data.Complex.BigOperators
explains:
  E2: [Complex, Complex.ext, Complex.mul_re, Complex.I_mul_I, Complex.normSq, Complex.normSq_mul, Complex.mul_conj, Complex.inv_def, Complex.mul_inv_cancel, Complex.re_sum]
  E1: auto
families: []
requires: [V02.C05, V02.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The complex numbers

### Overview

A complex number is a pair $(x, y)$ of real numbers, written $x + yi$. The sum is the sum of pairs, and the product obeys the rule $i^2 = -1$. These two operations make $\mathbb{C}$ a field that contains $\mathbb{R}$, and the conjugation $x + yi \mapsto x - yi$ is a ring automorphism of it. The quantity $z \bar z = x^2 + y^2$ is a real number that is not negative, and it is zero only at $z = 0$. This fact gives the inverse of each $z \neq 0$.

The module `Mathlib.Basic.Complex.Basic` holds this construction and its arithmetic. It defines the type `Complex` (notation `ℂ`), the cast `Complex.ofReal` from `ℝ`, the unit `Complex.I`, the conjugation as a star operation, the function `Complex.normSq`, and the instances of a commutative ring, of a field and of characteristic zero. The module `Mathlib.Basic.Complex.BigOperators` moves finite sums and products across the real part, the imaginary part and the cast. The modules `Mathlib.Data.Complex.Basic` and `Mathlib.Data.Complex.BigOperators` are deprecated redirects: they only import the two modules above.

The section uses the real numbers of Chapter 7 and the casts of Chapter 5. The norm $|z| = \sqrt{x^2 + y^2}$, the exponential function and the topology of $\mathbb{C}$ are not in these modules. The theorem that $\mathbb{C}$ is algebraically closed is `Complex.isAlgClosed`, in a module on polynomials.

### The library around it

#### The structure and its projections

`Complex` is a structure with two fields of type `ℝ`: the real part `Complex.re` and the imaginary part `Complex.im`. The constructor is `Complex.mk`, so `⟨x, y⟩ : ℂ` is the number $x + yi$. A complex number is fixed by its two parts. This is the extensionality lemma `Complex.ext`: if `z.re = w.re` and `z.im = w.im`, then `z = w`. The form with an `iff` is `Complex.ext_iff`. The tactic `ext` applies `Complex.ext` and leaves two real goals, one for each part. Most proofs of identities in `ℂ` have this shape: `ext`, then `simp`, then `ring` on each real goal.

The lemma `Complex.eta` states `⟨z.re, z.im⟩ = z`. The lemmas `Complex.forall` and `Complex.exists` replace a quantifier over `ℂ` with two quantifiers over `ℝ`. The equivalence `Complex.equivRealProd : ℂ ≃ ℝ × ℝ` sends $z$ to the pair $(\operatorname{re} z, \operatorname{im} z)$, and `Complex.equivRealProdAddHom` is the same map as an additive equivalence. The two projections are surjective: `Complex.re_surjective`, `Complex.im_surjective` and `Complex.range_re`.

#### The cast from ℝ and the casts from ℕ, ℤ and ℚ

The map `Complex.ofReal` sends $r$ to $\langle r, 0 \rangle$. It is a coercion, so `(r : ℂ)` means `Complex.ofReal r`. The lemmas `Complex.ofReal_re` and `Complex.ofReal_im` give its two parts, and `Complex.ofReal_inj` states that it is injective. The instance `Complex.canLift` lets a proof replace a complex number `z` with `z.im = 0` by a real number, with the tactic `lift`.

The cast keeps each operation. The lemmas have the names `Complex.ofReal_` followed by the name of the operation, and they carry the attributes `simp` and `norm_cast`.

| Lean name | Statement |
|---|---|
| `Complex.ofReal_zero` | $\uparrow 0 = 0$ |
| `Complex.ofReal_one` | $\uparrow 1 = 1$ |
| `Complex.ofReal_add` | $\uparrow(r + s) = \uparrow r + \uparrow s$ |
| `Complex.ofReal_neg` | $\uparrow(-r) = -\uparrow r$ |
| `Complex.ofReal_sub` | $\uparrow(r - s) = \uparrow r - \uparrow s$ |
| `Complex.ofReal_mul` | $\uparrow(r s) = \uparrow r \cdot \uparrow s$ |
| `Complex.ofReal_pow` | $\uparrow(r^n) = (\uparrow r)^n$ |
| `Complex.ofReal_inv` | $\uparrow(r^{-1}) = (\uparrow r)^{-1}$ |
| `Complex.ofReal_div` | $\uparrow(r / s) = \uparrow r / \uparrow s$ |
| `Complex.ofReal_zpow` | $\uparrow(r^n) = (\uparrow r)^n$ for $n \in \mathbb{Z}$ |

The bundled form is the ring homomorphism `Complex.ofRealHom : ℝ →+* ℂ`, and `Complex.ofRealHom_eq_coe` connects it with the coercion. The lemmas `Complex.ofReal_comp_add`, `Complex.ofReal_comp_mul` and `Complex.ofReal_comp_pow` state the same rules for functions $\alpha \to \mathbb{R}$, composed with the cast.

The casts from `ℕ`, `ℤ`, `ℚ≥0` and `ℚ` to `ℂ` are defined through `ℝ`. For example, the instance `Complex.instNatCast` sends $n$ to `ofReal n`. So `Complex.ofReal_natCast`, `Complex.ofReal_intCast` and `Complex.ofReal_ratCast` hold by `rfl`, and the parts of a cast are simple: `Complex.natCast_re`, `Complex.natCast_im`, `Complex.intCast_re` and `Complex.ratCast_re`. A numeral such as `(3 : ℂ)` is an `OfNat` literal, and `Complex.re_ofNat`, `Complex.im_ofNat` and `Complex.ofReal_ofNat` treat it.

#### Addition, multiplication and the unit i

The operations are defined part by part. The simp lemmas `Complex.add_re`, `Complex.add_im`, `Complex.neg_re`, `Complex.sub_re` and the others of this family compute the parts of a sum, a negation and a difference. The product is the main rule:

$$\operatorname{re}(z w) = \operatorname{re} z \operatorname{re} w - \operatorname{im} z \operatorname{im} w, \qquad \operatorname{im}(z w) = \operatorname{re} z \operatorname{im} w + \operatorname{im} z \operatorname{re} w.$$

These are `Complex.mul_re` and `Complex.mul_im`, and `Complex.mk_mul_mk` states the same rule for pairs. The lemmas `Complex.re_ofReal_mul` and `Complex.ofReal_mul'` treat a product with a real factor: $r \cdot \langle x, y \rangle = \langle r x, r y \rangle$.

The imaginary unit `Complex.I` is $\langle 0, 1 \rangle$, with `Complex.I_re` and `Complex.I_im`.

**Proposition.** $i \cdot i = -1$.

*Proof.* By `Complex.mul_re`, the real part of $i \cdot i$ is $0 \cdot 0 - 1 \cdot 1 = -1$. By `Complex.mul_im`, the imaginary part is $0 \cdot 1 + 1 \cdot 0 = 0$. These are the parts of $-1$, so `Complex.ext` gives the equality. $\square$

This is `Complex.I_mul_I`, and the simp lemma `Complex.I_sq` states $i^2 = -1$. Each complex number has the form $x + y i$: `Complex.mk_eq_add_mul_I` states $\langle a, b \rangle = a + b i$, and `Complex.re_add_im` states $\uparrow(\operatorname{re} z) + \uparrow(\operatorname{im} z) \cdot i = z$. The powers of $i$ have period $4$, by `Complex.I_pow_four` and `Complex.I_pow_eq_pow_mod`. The simproc `Complex.I_pow_eq_pow_mod'` reduces `I ^ n` for a literal $n \geq 4$ to `I ^ (n % 4)`, so `simp` computes $i^{10} = -1$ with no help. The form for an integer exponent is `Complex.I_zpow_eq_zpow_mod`. Other rules for $i$ are `Complex.I_ne_zero`, `Complex.I_mul`, `Complex.inv_I` ($i^{-1} = -i$) and `Complex.div_I`.

#### The ring instance and the scalar actions

The instance `Complex.commRing` makes `ℂ` a commutative ring. Each axiom is an identity in two real parts, and `ext`, `simp` and `ring` prove it. Before the ring instance, the module gives `Complex.addCommGroup` and `Complex.addGroupWithOne`. The module also adds short paths to the instances `Ring ℂ`, `CommSemiring ℂ` and others. Without them, the search for `Ring ℂ` could go through the field instance, and that instance is not computable.

A scalar action on `ℝ` extends to `ℂ` part by part: $r \bullet \langle x, y \rangle = \langle r \bullet x, r \bullet y \rangle$. This is the scoped instance `Complex.SMul.instSMulRealComplex`, with `Complex.smul_re` and `Complex.smul_im`. The instance is scoped because a global instance would let Lean search for `SMul ℂ ℂ` through `SMul ℂ ℝ`. The actions of `ℕ`, `ℤ`, `ℚ≥0` and `ℚ` on `ℂ` come from this instance, so the parts of `n • z` and `q • z` have simple forms: `Complex.re_nsmul` and `Complex.re_qsmul`, with their partners for `im`. The lemma `Complex.real_smul` states that `x • z = ↑x * z` for $x \in \mathbb{R}$. The maps `Complex.reAddGroupHom` and `Complex.imAddGroupHom` are the two projections as additive homomorphisms.

#### Conjugation

The conjugate of $z = \langle x, y \rangle$ is $\bar z = \langle x, -y \rangle$. Mathlib defines it as the operation `star` of an instance `StarRing ℂ`. The preferred form in statements is the ring homomorphism `starRingEnd ℂ`, with the notation `conj` from the scope `ComplexConjugate`. The lemma `Complex.star_def` connects `star` with `conj`. The simp lemmas `Complex.conj_re`, `Complex.conj_im`, `Complex.conj_ofReal` and `Complex.conj_I` give the conjugate of the basic numbers, and `Complex.conj_inv` states $\overline{z^{-1}} = (\bar z)^{-1}$.

A number is real exactly when it is its own conjugate. The module states this in three forms: `Complex.conj_eq_iff_real` with an existential, `Complex.conj_eq_iff_re` with the cast of the real part, and `Complex.conj_eq_iff_im` with the condition $\operatorname{im} z = 0$. The parts of $z$ come back from $z$ and $\bar z$:

$$z + \bar z = 2 \operatorname{re} z, \qquad z - \bar z = 2 \operatorname{im} z \cdot i.$$

These are `Complex.add_conj` and `Complex.sub_conj`. The forms that solve for the parts are `Complex.re_eq_add_conj` and `Complex.im_eq_sub_conj`.

#### The squared norm

The function `Complex.normSq` sends $z$ to $\operatorname{re} z \cdot \operatorname{re} z + \operatorname{im} z \cdot \operatorname{im} z$, by `Complex.normSq_apply`. It is a bundled monoid homomorphism with zero, of type `ℂ →*₀ ℝ`, so it keeps $0$, $1$ and products. The forms `Complex.normSq_mk` and `Complex.normSq_add_mul_I` compute it on $\langle x, y \rangle$ and on $x + y i$.

**Proposition (Multiplicativity).** $\operatorname{normSq}(z w) = \operatorname{normSq}(z) \operatorname{normSq}(w)$.

*Proof.* Let $z = a + bi$ and $w = c + di$. Then $z w = (ac - bd) + (ad + bc) i$, and

$$(ac - bd)^2 + (ad + bc)^2 = a^2 c^2 + b^2 d^2 + a^2 d^2 + b^2 c^2 = (a^2 + b^2)(c^2 + d^2),$$

because the two cross terms $-2abcd$ and $2abcd$ cancel. $\square$

This is `Complex.normSq_mul`.

**Proposition.** $z \bar z = \operatorname{normSq}(z)$, as a complex number.

*Proof.* With $z = x + y i$, the product $(x + y i)(x - y i)$ has the real part $x \cdot x - y \cdot (-y) = x^2 + y^2$ and the imaginary part $x \cdot (-y) + y \cdot x = 0$. $\square$

This is `Complex.mul_conj`, and `Complex.normSq_eq_conj_mul_self` is the form with the factors in the other order. The other facts about the squared norm are short.

| Lean name | Statement |
|---|---|
| `Complex.normSq_nonneg` | $0 \leq \operatorname{normSq} z$ |
| `Complex.normSq_eq_zero` | $\operatorname{normSq} z = 0 \iff z = 0$ |
| `Complex.normSq_pos` | $0 < \operatorname{normSq} z \iff z \neq 0$ |
| `Complex.normSq_ofReal` | $\operatorname{normSq} r = r \cdot r$ |
| `Complex.normSq_conj` | $\operatorname{normSq} \bar z = \operatorname{normSq} z$ |
| `Complex.normSq_neg` | $\operatorname{normSq}(-z) = \operatorname{normSq} z$ |
| `Complex.normSq_I` | $\operatorname{normSq} i = 1$ |
| `Complex.normSq_add` | $\operatorname{normSq}(z + w) = \operatorname{normSq} z + \operatorname{normSq} w + 2 \operatorname{re}(z \bar w)$ |
| `Complex.normSq_sub` | the same with $-2 \operatorname{re}(z \bar w)$ |
| `Complex.re_sq_le_normSq` | $\operatorname{re} z \cdot \operatorname{re} z \leq \operatorname{normSq} z$ |
| `Complex.im_sq_le_normSq` | $\operatorname{im} z \cdot \operatorname{im} z \leq \operatorname{normSq} z$ |

The proof of `Complex.normSq_eq_zero` uses that a sum of two real squares is zero only when both squares are zero.

#### The inverse and the field instance

The inverse is defined for each $z$ by $z^{-1} = \bar z \cdot \uparrow(\operatorname{normSq}(z)^{-1})$. This is `Complex.inv_def`. For $z = 0$ the formula gives $0 \cdot \uparrow(0^{-1}) = 0$, because $0^{-1} = 0$ in `ℝ`. So the junk value $0^{-1} = 0$ of `ℝ` passes to `ℂ`, and `Complex.inv_zero` holds.

**Proposition.** If $z \neq 0$, then $z z^{-1} = 1$.

*Proof.* By the definition and `Complex.mul_conj`, $z z^{-1} = (z \bar z) \cdot \uparrow(\operatorname{normSq}(z)^{-1}) = \uparrow(\operatorname{normSq}(z) \cdot \operatorname{normSq}(z)^{-1})$. Since $z \neq 0$, `Complex.normSq_eq_zero` gives $\operatorname{normSq}(z) \neq 0$, so the real product is $1$. $\square$

This is `Complex.mul_inv_cancel`, and with `Complex.inv_zero` it gives the instance `Complex.instField`. The parts of an inverse and a quotient are

$$\operatorname{re}(z^{-1}) = \frac{\operatorname{re} z}{\operatorname{normSq} z}, \quad \operatorname{im}(z^{-1}) = \frac{-\operatorname{im} z}{\operatorname{normSq} z}, \quad \operatorname{re}(z / w) = \frac{\operatorname{re} z \operatorname{re} w}{\operatorname{normSq} w} + \frac{\operatorname{im} z \operatorname{im} w}{\operatorname{normSq} w}.$$

These are `Complex.inv_re`, `Complex.inv_im` and `Complex.div_re`, with `Complex.div_im` for the imaginary part of a quotient. Division by a real number acts part by part: `Complex.div_ofReal`, `Complex.div_ofReal_re`, `Complex.div_natCast` and `Complex.div_ofNat_re`. The multiplicativity gives `Complex.normSq_inv` and `Complex.normSq_div`.

The field instance is noncomputable, because the inverse of `ℝ` is noncomputable. The instance `Complex.instRepr` prints a complex number as `x + y*I`, but the real parts print as Cauchy sequences.

**Proposition.** `ℂ` has characteristic zero.

*Proof.* The cast of $n \in \mathbb{N}$ to `ℂ` is the cast of $n$ to `ℝ`, followed by `Complex.ofReal`. Both maps are injective, and `ℝ` has characteristic zero. So $\uparrow n = 0$ in `ℂ` gives $n = 0$. $\square$

This is the instance `Complex.instCharZero`. With it, `norm_num` and `Nat.cast_inj` work in `ℂ`.

#### Rectangles in the plane

The set `s ×ℂ t` is `Complex.reProdIm s t`: the complex numbers with real part in $s$ and imaginary part in $t$. This is `Complex.mem_reProdIm`. It is the preimage of `s ×ˢ t` under `Complex.equivRealProd` (`Complex.preimage_equivRealProd_prod`), and the lemmas `Complex.reProdIm_subset_iff`, `Complex.reProdIm_nonempty` and `Complex.reProdIm_eq_empty` transfer from the product of sets. The set `Complex.Rectangle z w` is the closed rectangle with sides parallel to the axes and opposite corners $z$ and $w$. The lemmas `Complex.horizontalSegment_eq` and `Complex.verticalSegment_eq` describe the sides as images of real intervals.

#### Finite sums and products

The module `Mathlib.Basic.Complex.BigOperators` applies `map_sum` and `map_prod` to the maps of this section. For a finite set $s$ and $f : \alpha \to \mathbb{C}$,

$$\operatorname{re} \sum_{i \in s} f(i) = \sum_{i \in s} \operatorname{re} f(i), \qquad \operatorname{im} \sum_{i \in s} f(i) = \sum_{i \in s} \operatorname{im} f(i).$$

These are `Complex.re_sum` and `Complex.im_sum`. The proof is one line: `Complex.reAddGroupHom` is an additive homomorphism, so it commutes with finite sums. There is no rule for the real part of a product, because the real part is not multiplicative. The cast from `ℝ` is a ring homomorphism, so it commutes with both: `Complex.ofReal_sum` and `Complex.ofReal_prod`. The module has the same rules for the average `Finset.expect`, in `Complex.ofReal_expect` and `Complex.re_expect`, and for the function `Fintype.balance`, which subtracts the average from a function, in `Complex.ofReal_balance` and `Complex.re_balance`.

#### Common errors

1. A goal `z = w` in `ℂ` does not close with `ring` when it involves `z.re` or `z.im`. Use `ext` first, then `simp` to compute the parts with `Complex.mul_re` and the other part lemmas, and then `ring` on each real goal.
2. The notation `conj` is not available until `open ComplexConjugate`. Without it, the goal shows `(starRingEnd ℂ) z`. The lemmas about conjugation use this form, and a statement with `star z` needs `Complex.star_def` first.
3. `Complex.inv_def` and `Complex.inv_re` hold also at $z = 0$, with the junk value $0^{-1} = 0$. A statement such as $z z^{-1} = 1$ still needs the hypothesis $z \neq 0$, as in `Complex.mul_inv_cancel`.

### Exercises

1. (A) Compute the real and imaginary parts of $(2 + 3i)(1 - i)$ and of $(2 + 3i)^{-1}$ with `Complex.mul_re`, `Complex.mul_im`, `Complex.inv_re` and `Complex.inv_im`.
2. (A) Show that $\overline{z w} = \bar z \, \bar w$ by `ext` and the part lemmas, and explain why `map_mul` gives the same result for `starRingEnd ℂ`.
3. (B) Show that $z$ is real or purely imaginary if and only if $z^2$ is real. Use `Complex.conj_eq_iff_im` and the part lemmas.
4. (B) Use `Complex.normSq_mul` to show that a product of two sums of two integer squares is a sum of two integer squares. Write $65 = 5 \cdot 13$ as a sum of two squares in two ways.
5. (B) Prove $\operatorname{normSq}(z + w) + \operatorname{normSq}(z - w) = 2 \operatorname{normSq}(z) + 2 \operatorname{normSq}(w)$ from `Complex.normSq_add` and `Complex.normSq_sub`.
6. (C) Show that the only ring automorphisms of $\mathbb{C}$ that fix each real number are the identity and the conjugation. *Hint.* Such a map sends $i$ to a root of $x^2 + 1$.

### Reference

<?reference?>
