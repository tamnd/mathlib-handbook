---
title: Additive characters and shift maps
kind: api
modules:
  - Mathlib.Algebra.Group.AddChar
  - Mathlib.Algebra.AddConstMap.Basic
  - Mathlib.Algebra.AddConstMap.Equiv
  - Mathlib.Algebra.Group.Translate
  - Mathlib.Algebra.Group.ForwardDiff
explains:
  E2: [AddChar.map_neg_eq_inv, AddChar.inv_apply, AddChar.sum_eq_ite, AddConstMapClass.map_add_nsmul, AddConstEquiv.equivUnits, translate_translate, fwdDiff_addChar_eq, fwdDiff_iter_eq_factorial]
  E1: auto
families: []
requires: [V05.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Additive characters and shift maps

### Overview

A homomorphism sends a product to a product. Some maps of interest send a sum to a product, or a shifted argument to a shifted value. An *additive character* of an additive monoid $A$ with values in a monoid $M$ is a map $\psi : A \to M$ with $\psi(0) = 1$ and $\psi(a + b) = \psi(a) \psi(b)$. The map $x \mapsto e^{2 \pi i x / n}$ on $\mathbb{Z}/n\mathbb{Z}$ is the main example. A *shift map* is a map $f : G \to H$ with $f(x + a) = f(x) + b$ for fixed $a$ and $b$. The lift of a map of the circle to a map $\mathbb{R} \to \mathbb{R}$ with $f(x + 1) = f(x) + 1$ is the main example.

This section covers five small modules about such maps. The first gives the type of additive characters and its group structure. The next two give the bundled shift maps and the shift equivalences. The last two give two operators on functions on an additive group: the translation $\tau_a f (x) = f(x - a)$ and the forward difference $\Delta_h f (x) = f(x + h) - f(x)$. Each of these objects is a homomorphism in disguise, and the section shows the disguise. The type tags of Chapter 1 give the link with ordinary homomorphisms.

### The library around it

#### Additive characters

The module `Mathlib.Algebra.Group.AddChar` defines the structure `AddChar A M`, for an additive monoid $A$ and a monoid $M$. Its fields are the function and the two laws, and the lemmas `AddChar.map_zero_eq_one` and `AddChar.map_add_eq_mul` state the laws for the coercion to functions. The extensionality lemma is `AddChar.ext`.

An additive character is a homomorphism from the multiplicative copy of $A$ to $M$. The equivalence `AddChar.toMonoidHomEquiv` identifies `AddChar A M` with `Multiplicative A →* M`, and `AddChar.toAddMonoidHomEquiv` identifies it with `A →+ Additive M`. These equivalences let each lemma about homomorphisms pass to characters. Two of them are stated directly:

| Lean name | Statement |
| --- | --- |
| `AddChar.map_nsmul_eq_pow` | $\psi(n \cdot x) = \psi(x)^n$ for $n \in \mathbb{N}$ |
| `AddChar.map_zsmul_eq_zpow` | $\psi(n \cdot x) = \psi(x)^n$ for $n \in \mathbb{Z}$, when $A$ is a group |
| `AddChar.map_neg_eq_inv` | $\psi(-a) = \psi(a)^{-1}$, when $A$ is a group |
| `AddChar.map_sub_eq_div` | $\psi(a - b) = \psi(a) / \psi(b)$ |
| `AddChar.val_isUnit` | $\psi(a)$ is a unit, when $A$ is a group |

**Theorem (Characters send negatives to inverses).** Let $A$ be an additive group and $M$ a division monoid. Then $\psi(-a) = \psi(a)^{-1}$.

*Proof.* $\psi(-a) \psi(a) = \psi(-a + a) = \psi(0) = 1$. In a division monoid an element $u$ with $u v = 1$ is $v^{-1}$. $\square$

For a group $A$ and any monoid $M$, the same computation shows that $\psi(a)$ has the two-sided inverse $\psi(-a)$, which is `AddChar.val_isUnit`.

#### The group of characters

Let $M$ be commutative. The pointwise product of two characters is a character, since $\psi(a + b) \chi(a + b) = \psi(a) \chi(a) \psi(b) \chi(b)$. So `AddChar A M` is a commutative monoid, by `AddChar.instCommMonoid`. The character group is the dual of $A$, and a dual is usually written additively. So the library gives `AddChar A M` both structures: `AddChar.instAddCommMonoid` writes the same operation as a sum. The lemma `AddChar.mul_eq_add` says $\psi \chi = \psi + \chi$, and `AddChar.one_eq_zero` says that the two neutral elements are the trivial character $a \mapsto 1$. The evaluation lemmas for the sum are `AddChar.add_apply` and `AddChar.zero_apply`. For the product they are the general lemmas `mul_apply` and `one_apply`, which apply through the instances `AddChar.instIsMulApply` and `AddChar.instIsOneApply`.

When $A$ is a commutative group, the characters form a group, by `AddChar.instCommGroup` and `AddChar.instAddCommGroup`. The inverse does not need inverses in $M$.

**Theorem (The inverse character).** Let $A$ be a commutative additive group. The inverse of $\psi$ is the character $a \mapsto \psi(-a)$.

*Proof.* The map $a \mapsto \psi(-a)$ is a character, because $-(a + b) = -a + -b$ in a commutative group. Its product with $\psi$ is $a \mapsto \psi(-a) \psi(a) = \psi(0) = 1$, the trivial character. $\square$

This is `AddChar.inv_apply`. When $M$ is a division monoid, `AddChar.inv_apply'` gives the form $\psi^{-1}(a) = \psi(a)^{-1}$. The lemma `AddChar.injective_iff` says that $\psi$ is injective if and only if $\psi(x) = 1$ implies $x = 0$, the kernel test of homomorphisms.

Maps act on characters on both sides. A homomorphism $f : A \to B$ sends a character of $B$ to the character `AddChar.compAddMonoidHom φ f` of $A$. A homomorphism $f : M \to N$ sends a character with values in $M$ to `MonoidHom.compAddChar f φ`. When $A$ is a ring $R$, the character `AddChar.mulShift ψ r` is $x \mapsto \psi(r x)$. The lemmas `AddChar.mulShift_mul` and `AddChar.mulShift_mulShift` say $\psi_r \psi_s = \psi_{r+s}$ and $(\psi_r)_s = \psi_{r s}$. The map `AddChar.doubleDualEmb` sends $a \in A$ to the character $\psi \mapsto \psi(a)$ of the dual group.

The module ends with the first orthogonality relation.

**Theorem (Sum of a character).** Let $A$ be a finite additive group and $R$ a commutative domain. For a character $\psi : A \to R$, $\sum_{a \in A} \psi(a) = |A|$ if $\psi$ is trivial, and $\sum_{a \in A} \psi(a) = 0$ otherwise.

*Proof.* If $\psi$ is trivial, each term is $1$. Otherwise choose $x$ with $\psi(x) \neq 1$. The map $a \mapsto a + x$ is a bijection of $A$, so $S = \sum_a \psi(a) = \sum_a \psi(a + x) = \psi(x) S$. Thus $(\psi(x) - 1) S = 0$, and $S = 0$ because $\psi(x) - 1 \neq 0$. $\square$

This is `AddChar.sum_eq_ite`, stated with the zero of the additive structure for the trivial character. The forms `AddChar.sum_eq_zero_iff_ne_zero` and `AddChar.sum_ne_zero_iff_eq_zero` need characteristic zero.

#### Shift maps

The module `Mathlib.Algebra.AddConstMap.Basic` defines the structure `AddConstMap G H a b` of maps $f : G \to H$ with $f(x + a) = f(x) + b$ for all $x$. The scoped notation `G →+c[a, b] H` is in the namespace `AddConstMap`. The class `AddConstMapClass` is the morphism class of such maps, in the style of the morphism classes of Section 3. A shift map semiconjugates the shift by $a$ to the shift by $b$, and `AddConstMapClass.semiconj` states this with `Function.Semiconj`.

**Theorem (Multiples of the shift).** Let $f(x + a) = f(x) + b$ for all $x$. Then $f(x + n a) = f(x) + n b$ for each $n \in \mathbb{N}$.

*Proof.* Use induction on $n$. For $n = 0$ both sides are $f(x)$. Then $f(x + (n + 1) a) = f((x + n a) + a) = f(x + n a) + b = f(x) + n b + b$. $\square$

This is `AddConstMapClass.map_add_nsmul`. The module has the same result for many forms of the argument: `AddConstMapClass.map_add_zsmul` for an integer $n$ in a group, `AddConstMapClass.map_sub_const` for $f(x - a) = f(x) - b$, and `AddConstMapClass.map_add_nat` and `AddConstMapClass.map_add_int` for maps of type $[1, 1]$, where $f(x + n) = f(x) + n$. For a map $f : R \to H$ of type $[1, b]$ on a floor ring, `AddConstMapClass.map_fract` gives $f(\operatorname{fract} x) = f(x) - \lfloor x \rfloor \cdot b$. So such a map is fixed by its values on $[0, 1)$, and `AddConstMap.mkFract` gives the equivalence between these maps and the functions on $[0, 1)$. On an Archimedean ordered group, `AddConstMapClass.monotone_iff_Icc` reduces the monotonicity of a shift map with $a > 0$ to its monotonicity on one closed interval $[l, l + a]$.

The maps $G \to G$ of type $[a, a]$ compose, so they form a monoid, by `AddConstMap.instMonoid`. The product is the composition, by `AddConstMap.mul_def`, and the power is the iterate, by the general lemma `FunLike.coe_pow_eq_iterate` through the instance `AddConstMap.instIsNPowApplyEqIterate`. The homomorphism `AddConstMap.toEnd` sends such a map to the monoid of all maps $G \to G$.

The module `Mathlib.Algebra.AddConstMap.Equiv` gives the bijective shift maps, `AddConstEquiv G H a b`, with `AddConstEquiv.refl`, `AddConstEquiv.symm` and `AddConstEquiv.trans`. The equivalences $G \to G$ of type $[a, a]$ form a group, by `AddConstEquiv.instGroup`.

**Theorem (Equivalences are the units).** The group of shift equivalences of type $[a, a]$ is isomorphic to the unit group of the monoid of shift maps of type $[a, a]$.

*Proof sketch.* An equivalence $e$ gives the unit with value $e$ and inverse $e^{-1}$, since the inverse of a shift map is a shift map: $e^{-1}(y + a) = e^{-1}(y) + a$ follows from $e(e^{-1}(y) + a) = y + a$. A unit $u$ with inverse $v$ gives the equivalence with the maps $u$ and $v$. The two constructions are inverse, and they respect products. $\square$

This is `AddConstEquiv.equivUnits`. The homomorphism `AddConstEquiv.toPerm` sends a shift equivalence to its permutation of $G$.

#### Translation of functions

The module `Mathlib.Algebra.Group.Translate` defines `translate a f`, the function $x \mapsto f(x - a)$, for a commutative additive group $G$. The scoped notation `τ` is in the namespace `translate`. The minus sign makes translation a left action: $\tau_a \tau_b = \tau_{a+b}$.

**Theorem (Translations compose).** $\tau_a(\tau_b f) = \tau_{a + b} f$.

*Proof.* $\tau_a(\tau_b f)(x) = \tau_b f(x - a) = f(x - a - b) = f(x - (a + b))$. $\square$

This is `translate_translate`. With `translate_zero` it says that translation is an action of $G$ on the functions $G \to \alpha$. The lemma `translate_eq_domAddActMk_vadd` identifies it with the action of the domain group, and `translate_comm` says that two translations commute. Translation is linear in $f$, by `translate_add_right`, `translate_smul_right` and `translate_sum_right`. The support moves with the function, by `support_translate`, and on a finite group the sum does not change, by `sum_translate`.

#### Forward differences

The module `Mathlib.Algebra.Group.ForwardDiff` defines `fwdDiff h f`, the function $y \mapsto f(y + h) - f(y)$, for $f$ from an additive commutative monoid to an additive commutative group. The scoped notation `Δ_[h]` is in the namespace `fwdDiff`. The operator is additive, by `fwdDiff_add` and `fwdDiff_finsetSum`, and it commutes with constant scalars, by `fwdDiff_const_smul`. The product rule is `fwdDiff_smul`. The lemmas for the iterate $\Delta_h^n$ have names that start with fwdDiff_iter, such as `fwdDiff_iter_add`.

The two main formulas are the expansions of Newton. The lemma `fwdDiff_iter_eq_sum_shift` gives $\Delta_h^n f(y) = \sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} f(y + k h)$. The lemma `shift_eq_sum_fwdDiff_iter` gives the inverse formula $f(y + n h) = \sum_{k=0}^{n} \binom{n}{k} \Delta_h^k f(y)$. Additive characters are the eigenfunctions of the operator.

**Theorem (Differences of a character).** Let $\varphi : M \to R$ be an additive character with values in a ring. Then $\Delta_h^n \varphi(x) = (\varphi(h) - 1)^n \varphi(x)$.

*Proof.* For $n = 1$, $\Delta_h \varphi(x) = \varphi(x + h) - \varphi(x) = \varphi(h) \varphi(x) - \varphi(x) = (\varphi(h) - 1) \varphi(x)$. So $\Delta_h \varphi$ is $c \varphi$ with the constant $c = \varphi(h) - 1$. The operator commutes with multiplication by a constant, so induction on $n$ gives the result. $\square$

This is `fwdDiff_addChar_eq`. Over a commutative ring, the differences of the powers give the factorial.

**Theorem (Differences of a power).** With step $1$, $\Delta^n (r \mapsto r^n)$ is the constant $n!$, and $\Delta^n (r \mapsto r^j) = 0$ for $j < n$.

*Proof sketch.* The difference $\Delta (r^j) = (r + 1)^j - r^j$ is a polynomial of degree $j - 1$ with leading coefficient $j$, by the binomial theorem. Each difference lowers the degree by one and multiplies the leading coefficient by the degree. After $n$ steps the power $r^n$ gives the constant $n \cdot (n-1) \cdots 1 = n!$, and a power of lower degree gives $0$. $\square$

These are `fwdDiff_iter_eq_factorial` and `fwdDiff_iter_pow_eq_zero_of_lt`. The polynomial forms are `Polynomial.fwdDiff_iter_degree_eq_factorial` and `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`. For binomial coefficients, `fwdDiff_choose` gives Pascal's rule $\Delta \binom{x}{j+1} = \binom{x}{j}$.

#### Common errors

1. `AddChar A M` has two structures on the same operation, a product and a sum. A goal can contain `ψ * χ` while a lemma states `ψ + χ`. Rewrite with `AddChar.mul_eq_add` or `AddChar.one_eq_zero` to match the forms. In particular, the trivial character is `0` in `AddChar.sum_eq_ite`.
2. The notations `→+c[a, b]`, `τ` and `Δ_[h]` are scoped. Without `open AddConstMap`, `open translate` or `open fwdDiff` they do not parse, and the long names `AddConstMap G H a b`, `translate a f` and `fwdDiff h f` must be used.
3. `translate a f` is $x \mapsto f(x - a)$, not $x \mapsto f(x + a)$. The forward difference uses $f(y + h)$. A computation that mixes the two operators must track the sign.

### Exercises

1. (A) Prove `AddChar.map_nsmul_eq_pow` by induction on $n$, from `AddChar.map_zero_eq_one` and `AddChar.map_add_eq_mul`.
2. (A) Show that $\tau_a$ and $\tau_{-a}$ are inverse maps on the functions $G \to \alpha$, with `translate_translate` and `translate_zero`.
3. (B) Let $\zeta$ be an element of a commutative monoid $M$ with $\zeta^n = 1$. Construct the additive character of $\mathbb{Z}/n\mathbb{Z}$ with $\psi(1) = \zeta$, and show that each character of $\mathbb{Z}/n\mathbb{Z}$ has this form.
4. (B) Let $f : \mathbb{R} \to \mathbb{R}$ satisfy $f(x + 1) = f(x) + 1$. Show that $x \mapsto f(x) - x$ has period $1$, and that each function $g$ of period $1$ gives such an $f$ by $f(x) = x + g(x)$.
5. (B) Use `fwdDiff_iter_eq_sum_shift` and `fwdDiff_iter_eq_factorial` to prove $\sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} k^n = n!$.
6. (C) Let $A$ be a finite commutative group and $R$ a domain. Show that two different characters $\psi, \chi : A \to R$ satisfy $\sum_{a} \psi(a) \chi(-a) = 0$. Hint: apply `AddChar.sum_eq_ite` to the character $\psi - \chi$.

### Reference

<?reference?>
