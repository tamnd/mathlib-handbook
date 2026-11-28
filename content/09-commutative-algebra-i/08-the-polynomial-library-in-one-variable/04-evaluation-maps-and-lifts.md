---
title: Evaluation, maps and lifts
kind: api
modules:
  - Mathlib.Algebra.Polynomial.Eval.Defs
  - Mathlib.Algebra.Polynomial.Eval.Coeff
  - Mathlib.Algebra.Polynomial.Eval.Degree
  - Mathlib.Algebra.Polynomial.Eval.Algebra
  - Mathlib.Algebra.Polynomial.Eval.SMul
  - Mathlib.Algebra.Polynomial.Eval.Subring
  - Mathlib.Algebra.Polynomial.Eval.Irreducible
  - Mathlib.Algebra.Polynomial.AlgebraMap
  - Mathlib.Algebra.Polynomial.Lifts
  - Mathlib.Algebra.Polynomial.Smeval
  - Mathlib.Algebra.Polynomial.DenomsClearable
  - Mathlib.Algebra.Polynomial.GroupRingAction
explains:
  E2: [Polynomial.eval₂_eq_sum, Polynomial.eval_comp, Polynomial.coeff_map, Polynomial.eval₂_hom, Polynomial.aeval_def, Polynomial.eval_unique, Polynomial.lifts_and_degree_eq_and_monic, Polynomial.aeval_eq_smeval, one_le_pow_mul_abs_eval_div, prodXSubSMul.coeff]
  E1: auto
families: []
requires: [V06.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Evaluation, maps and lifts

### Overview

A polynomial $p \in R[X]$ becomes a function when a value is put in for $X$. The library has one basic construction for this, `Polynomial.eval₂`. For a ring map $f \colon R \to S$ and an element $x \in S$, it computes $\sum_n f(a_n) x^n$. Evaluation at a point of $R$, composition of polynomials, the map of coefficients along $f$ and the evaluation in an $R$-algebra are all special cases. So most lemmas in this section are proved once for `eval₂` and then copied.

The section covers the files in the order of their dependencies. `Mathlib.Algebra.Polynomial.Eval.Defs` defines the maps, the other files of `Mathlib.Algebra.Polynomial.Eval` add facts about coefficients, degrees, scalars and subrings, and `Mathlib.Algebra.Polynomial.AlgebraMap` gives the algebra structure and `Polynomial.aeval`. Three smaller files follow: the polynomials that lift along a ring map, the evaluation in a module with powers, and the bound that clears denominators. The last file lets a group act on $R[X]$ through its action on $R$.

### The library around it

#### The map eval₂

The definition `Polynomial.eval₂` takes $f \colon R \to+* S$, $x \in S$ and $p \in R[X]$. The lemma `Polynomial.eval₂_eq_sum` gives its value as the sum over the support, $\operatorname{eval₂} f\, x\, p = \sum_e f(a_e)\, x^e$. Over a finite range it is `Polynomial.eval_eq_sum_range`. The simp set has the lemmas `Polynomial.eval₂_C`, `Polynomial.eval₂_X`, `Polynomial.eval₂_add`, `Polynomial.eval₂_monomial` and `Polynomial.eval₂_pow`.

The product rule needs care. `Polynomial.eval₂_mul` holds when $S$ is commutative. Proof: both sides are additive in $p$ and in $q$, so it is enough to check monomials. For $p = a X^m$ and $q = b X^n$ the left side is $f(a) f(b)\, x^{m+n}$ and the right side is $f(a)\, x^m f(b)\, x^n$. They agree when $x^m$ commutes with $f(b)$. Without commutativity, `Polynomial.eval₂_mul_noncomm` asks for this hypothesis on the coefficients of $q$. The bundled forms are `Polynomial.eval₂AddMonoidHom`, `Polynomial.eval₂RingHom` for commutative $S$ and `Polynomial.eval₂RingHom'` with a commutation hypothesis.

Evaluation at a point of $R$ is `Polynomial.eval` $x$ $p$, which is `eval₂` with the identity map. The ring map is `Polynomial.evalRingHom`. The predicate `Polynomial.IsRoot` $p$ $a$ means `eval a p = 0`, by `Polynomial.IsRoot.def`. Over a ring without zero divisors `Polynomial.root_mul` says that $a$ is a root of $pq$ exactly when it is a root of $p$ or of $q$. The lemma `Polynomial.coeff_zero_eq_eval_zero` reads the constant term as the value at $0$.

#### Composition

The composition `Polynomial.comp` $p$ $q$ is $p(q)$, defined as `eval₂ C q p`. The key rule `Polynomial.eval_comp` says $(p \circ q)(x) = p(q(x))$ over a commutative semiring. Proof: the map $p \mapsto \operatorname{eval}_x(p \circ q)$ is a ring map $R[X] \to R$ that sends $C a$ to $a$ and $X$ to $q(x)$. The map $p \mapsto p(q(x))$ has the same properties, and two ring maps out of $R[X]$ that agree on $C$ and on $X$ are equal. From this `Polynomial.comp_assoc` follows, and `Polynomial.compRingHom` is the ring map $p \mapsto p \circ q$. The degree of a composition comes from `Polynomial.coeff_comp_degree_mul_degree`: the coefficient of $X^{mn}$ in $p \circ q$ is $\operatorname{lc}(p)\, \operatorname{lc}(q)^m$ when $m = \deg p$, $n = \deg q$ and $n \ne 0$.

#### The map of coefficients

For $f \colon R \to+* S$, `Polynomial.map` $f$ applies $f$ to each coefficient. It is defined as `eval₂ (C.comp f) X`, and `Polynomial.coeff_map` gives the coefficients: $(\operatorname{map} f\, p)_n = f(p_n)$. Proof: both sides are additive in $p$, and on a monomial $a X^m$ the left side is the coefficient of $X^n$ in $C(f(a)) X^m$. The value is `Polynomial.eval_map`: evaluating $\operatorname{map} f\, p$ at $x$ is $\operatorname{eval₂} f\, x\, p$. Read from right to left, `Polynomial.eval₂_eq_eval_map` replaces an `eval₂` by an `eval`, which is often the better normal form.

| Lean name | Statement |
| --- | --- |
| `Polynomial.map_map` | $\operatorname{map} g \circ \operatorname{map} f = \operatorname{map} (g \circ f)$ |
| `Polynomial.map_injective` | an injective $f$ gives an injective `map f` |
| `Polynomial.map_surjective` | a surjective $f$ gives a surjective `map f` |
| `Polynomial.mapRingHom` | `map f` as a ring map |
| `Polynomial.mapEquiv` | a ring isomorphism $R \cong S$ gives $R[X] \cong S[X]$ |
| `Polynomial.piEquiv` | $(\prod_i R_i)[X] \cong \prod_i R_i[X]$ for a finite index set |
| `Polynomial.degree_map_le` | $\deg(\operatorname{map} f\, p) \le \deg p$ |
| `Polynomial.natDegree_map_of_leadingCoeff_ne_zero` | equality if $f(\operatorname{lc} p) \ne 0$ |
| `Polynomial.isRoot_map_iff` | for injective $f$, $f(x)$ is a root of the image exactly when $x$ is a root |

The lemma `Polynomial.eval₂_hom` says that $\operatorname{eval₂} f\, (f(x))\, p = f(p(x))$. Proof: both sides are additive in $p$, and for $p = a X^n$ both are $f(a) f(x)^n$ because $f$ is multiplicative. The general form is `Polynomial.hom_eval₂`.

The small files add one topic each. `Mathlib.Algebra.Polynomial.Eval.SMul` has `Polynomial.eval_smul` and the linear map `Polynomial.leval`. `Mathlib.Algebra.Polynomial.Eval.Subring` has `Polynomial.mem_map_range`: a polynomial over $S$ lies in the range of `mapRingHom f` exactly when each coefficient lies in the range of $f$. `Mathlib.Algebra.Polynomial.Eval.Irreducible` says that a monic polynomial is irreducible if its image along a map of domains is irreducible. `Mathlib.Algebra.Polynomial.Eval.Algebra` has `Polynomial.eval₂_mul'`, the product rule for `algebraMap` into a noncommutative algebra.

#### The algebra structure and aeval

For a commutative semiring $R$ and an $R$-algebra $A$, the type $A[X]$ is an $R$-algebra. The map `algebraMap R R[X]` is `C`, by `Polynomial.C_eq_algebraMap`, and `Polynomial.algebraMap_apply` gives the general case. The evaluation `Polynomial.aeval` $x$ is the $R$-algebra map $R[X] \to A$ that sends $X$ to $x$. By `Polynomial.aeval_def` it is `eval₂ (algebraMap R A) x`. This is the form to use in field theory and linear algebra, where $x$ is an element of an extension field or an endomorphism.

The universal property is `Polynomial.eval_unique`: an algebra map $\varphi \colon R[X] \to A$ satisfies $\varphi(p) = \operatorname{eval₂}(\operatorname{algebraMap})\, (\varphi X)\, p$. Proof: both sides are algebra maps that agree on $X$, and $X$ generates $R[X]$ as an $R$-algebra, so they agree everywhere (`Polynomial.algHom_ext`). So the algebra maps out of $R[X]$ correspond to the elements of $A$, which is the equivalence `Polynomial.aevalEquiv`. The lemma `Polynomial.aeval_algHom_apply` moves an algebra map through `aeval`, and `Polynomial.comp_eq_aeval` writes composition as `aeval`.

Other maps in `Mathlib.Algebra.Polynomial.AlgebraMap`:

| Lean name | Use |
| --- | --- |
| `Polynomial.mapAlg` | $R[X] \to S[X]$ as an $R$-algebra map |
| `Polynomial.mapAlgHom` | an algebra map $A \to B$ gives $A[X] \to B[X]$ |
| `Polynomial.eval₂AlgHom` | `eval₂` as an algebra map, with a commutation hypothesis |
| `Polynomial.aevalTower` | evaluation of $R[X]$ in a tower $S \to R \to A'$ |
| `Polynomial.aeval_endomorphism` | the value of $p(f)$ on a vector $v$ |
| `Polynomial.algEquivAevalXAddC` | the automorphism $X \mapsto X + c$ |
| `Polynomial.algEquivOfCompEqX` | an automorphism from two inverse polynomials |

The lemma `Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero` says that $p \mid q$ and $p(x) = 0$ give $q(x) = 0$. It is the reason a minimal polynomial divides every polynomial that vanishes at $x$. The lemma `Polynomial.mem_nonZeroDivisors_iff` says that $P$ is a nonzero divisor of $R[X]$ exactly when no nonzero scalar kills it.

#### Polynomials that lift

For $f \colon R \to+* S$, the subsemiring `Polynomial.lifts` $f$ is the range of `mapRingHom f`, and `Polynomial.liftsRing` is the same subring for rings. By `Polynomial.mem_lifts`, $p$ lifts when $p = \operatorname{map} f\, q$ for some $q$. By `Polynomial.lifts_iff_coeff_lifts`, this holds exactly when each coefficient lies in the range of $f$. So every polynomial lifts along a surjective map (`Polynomial.mem_lifts_of_surjective`).

A lift can be chosen with good properties. `Polynomial.lifts_and_degree_eq_and_monic` says that a monic polynomial that lifts has a monic lift of the same degree. Proof: let $n = \deg p$ and choose $g_k \in R$ with $f(g_k) = p_k$ for $k < n$. Put $q = X^n + \sum_{k < n} g_k X^k$. Then $\operatorname{map} f\, q = p$, because the top coefficient of $p$ is $1 = f(1)$, and $q$ is monic of degree $n$ by construction. The variant with the natural degree is `Polynomial.lifts_and_natDegree_eq_and_monic`. These results are used for integral elements and for reduction modulo a prime.

#### Evaluation with scalar multiplication

The file `Mathlib.Algebra.Polynomial.Smeval` evaluates $p \in R[X]$ at an element $x$ of a type $S$ that has an action of $R$ and powers, but need not be an $R$-algebra. The value `Polynomial.smeval` $p$ $x$ is $\sum_n a_n \cdot x^n$. Two comparisons connect it with the other maps: `Polynomial.eval_eq_smeval` for $S = R$, and `Polynomial.aeval_eq_smeval` for an $R$-algebra $S$. Proof of the second: both sides are additive in $p$, and on $a X^n$ the left side is $\operatorname{algebraMap}(a) x^n$ and the right side is $a \cdot x^n$, which agree by `Algebra.smul_def`. The product rule `Polynomial.smeval_mul` needs power associativity and the scalar tower conditions, and `Polynomial.smeval_commute` says that values at commuting points commute. The construction is used for binomial rings, where $S$ need not be associative.

#### Clearing denominators

The file `Mathlib.Algebra.Polynomial.DenomsClearable` has a predicate and one bound. The predicate `DenomsClearable a b N f i` says that $b$ is invertible in $K$ along $i \colon R \to K$ and that $i(b)^N f(i(a)/i(b))$ is the image of an element of $R$. The lemma `denomsClearable_natDegree` says that this holds for $N = \deg f$. The bound `one_le_pow_mul_abs_eval_div` says: for $f \in \mathbb{Z}[X]$, integers $a, b$ with $b > 0$, and $f(a/b) \ne 0$ in an ordered field $K$, $1 \le b^{\deg f}\, |f(a/b)|$. Proof: by `denomsClearable_natDegree`, $b^{\deg f} f(a/b)$ is the image of an integer $D$. This integer is not zero, so $|D| \ge 1$. This is the lower bound used to prove that some numbers are transcendental.

#### Group actions on polynomials

For a monoid $M$ that acts on $R$ by ring automorphisms, the instance `Polynomial.instMulSemiringAction` makes $M$ act on $R[X]$ on the coefficients. By `Polynomial.smul_eq_map` the action of $m$ is `map` along the ring map of $m$, and `Polynomial.smul_eval_smul` says $(m \cdot f)(m \cdot x) = m \cdot f(x)$. A finite group $G$ gives the polynomial `prodXSubSMul G R x`, the product of $X - y$ over the distinct elements $y$ of the orbit of $x$. It is monic (`prodXSubSMul.monic`) and has $x$ as a root (`prodXSubSMul.eval`). The lemma `prodXSubSMul.coeff` says that its coefficients are fixed by $G$. Proof: $g$ permutes the orbit of $x$, so it permutes the factors $X - y$, and the product does not change. So $x$ is a root of a monic polynomial with coefficients in the invariant subring, and $R$ is integral over $R^G$. The map `MulSemiringActionHom.polynomial` extends an equivariant ring map to polynomials.

#### Common errors

1. Using `Polynomial.eval₂_mul` over a noncommutative target. The lemma needs a commutative $S$. Over a matrix ring or an endomorphism ring, use `Polynomial.aeval`, which is an algebra map, or `Polynomial.eval₂_mul_noncomm`.
2. Mixing `eval₂ f x p`, `eval x (map f p)` and `aeval x p` in one proof. The simp set does not always choose the same form. Rewrite with `Polynomial.eval₂_eq_eval_map` or `Polynomial.aeval_def` to one normal form first.
3. Reading `Polynomial.comp p q` as $q \circ p$. It is $p(q)$, the polynomial $p$ with $q$ put in for $X$.

### Exercises

1. (A) Use `Polynomial.eval_comp` to compute $(X^2 + 1) \circ (X - 1)$ at $x = 3$ in two ways.
2. (A) Show with `Polynomial.coeff_map` that the reduction modulo $2$ of $3X^2 + 4X + 1$ is $X^2 + 1$ in $(\mathbb{Z}/2)[X]$.
3. (B) Prove that `Polynomial.aeval` at $x$ and `Polynomial.eval₂` along `algebraMap` at $x$ have the same kernel.
4. (B) Show that every polynomial over $\mathbb{Z}/n$ lifts to $\mathbb{Z}[X]$, and that a monic one lifts to a monic polynomial of the same degree.
5. (B) Use `one_le_pow_mul_abs_eval_div` to show that $|\sqrt{2} - a/b| \ge 1/(b^2 (|\sqrt{2}| + |a/b|))$ for integers $a$ and $b > 0$.
6. (C) Let a finite group $G$ act on a commutative ring $R$. Use `prodXSubSMul.coeff` to show that every element of $R$ is integral over the invariant subring.

### Reference

<?reference?>
