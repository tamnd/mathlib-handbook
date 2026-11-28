---
title: Opposite and symmetrized structures
kind: api
modules:
  - Mathlib.Algebra.Opposites
  - Mathlib.Algebra.Symmetrized
  - Mathlib.Algebra.Group.Opposite
  - Mathlib.Algebra.Group.Equiv.Opposite
explains:
  E2: [MulOpposite, MulOpposite.op_mul, MulOpposite.op_injective, MulOpposite.rec', SymAlg, SymAlg.sym_mul_sym, SymAlg.mul_comm, SymAlg.instIsCommJordan]
  E1: auto
families: []
requires: [V01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Opposite and symmetrized structures

### Overview

Let $M$ be a monoid. The opposite monoid $M^{\mathrm{op}}$ has the same elements and the product in the other order: $a * b = b a$. It is again a monoid, and it is commutative if and only if $M$ is. The opposite turns a right action into a left action, a right ideal into a left ideal and an antihomomorphism into a homomorphism. So one proof about left structures gives the result about right structures, through the opposite.

Mathlib gives the opposite as a new type `MulOpposite`, with a map `MulOpposite.op` into it and a map `MulOpposite.unop` back. The module `Mathlib.Algebra.Opposites` defines the type, the two maps and the operations on the level of notation. The module `Mathlib.Algebra.Symmetrized` gives a second construction on the same pattern, the symmetrized algebra `SymAlg`. Its product is $a \circ b = \frac12 (a b + b a)$, and it is a commutative Jordan algebra. Both types follow one method: a new type has the same elements and carries a second structure. The type `ConjAct` of Chapter 6 is another example.

### The library around it

#### The type and its two maps

The type `MulOpposite` of a type $\alpha$ is a structure with one field. It is not the type $\alpha$ itself. So Lean does not confuse the product of $\alpha$ with the product of its opposite. The additive opposite `AddOpposite` reverses the sum instead. Both are built on the auxiliary structure `PreOpposite`, and so the two opposites of a type are equal by definition.

The maps `MulOpposite.op` and `MulOpposite.unop` are inverse bijections.

| Lean name | Statement |
|---|---|
| `MulOpposite.unop_op` | $\mathrm{unop}(\mathrm{op}\ x) = x$ |
| `MulOpposite.op_unop` | $\mathrm{op}(\mathrm{unop}\ x) = x$ |
| `MulOpposite.op_comp_unop` | $\mathrm{op} \circ \mathrm{unop} = \mathrm{id}$ |
| `MulOpposite.op_injective` | $\mathrm{op}$ is injective |
| `MulOpposite.op_surjective` | $\mathrm{op}$ is surjective |
| `MulOpposite.op_bijective` | $\mathrm{op}$ is bijective |
| `MulOpposite.op_inj` | $\mathrm{op}\ x = \mathrm{op}\ y \iff x = y$ |
| `MulOpposite.opEquiv` | the bijection $\alpha \simeq \alpha^{\mathrm{op}}$ as an equivalence |

The first two are simp lemmas, so simp removes a pair of maps. The proof of `MulOpposite.op_injective` is one line: apply `MulOpposite.unop` to both sides of $\mathrm{op}\ x = \mathrm{op}\ y$ and use `MulOpposite.unop_op`. The same argument for `MulOpposite.unop` gives `MulOpposite.unop_injective`, and the two inverse maps give surjectivity.

To prove a statement for each element of the opposite, write the element as $\mathrm{op}\ x$. The recursor `MulOpposite.rec'` does this, and it is the default eliminator: the tactic *induction x* on $x$ in the opposite gives the goal for $\mathrm{op}\ x$ with $x$ in $\alpha$. The lemmas `MulOpposite.forall` and `MulOpposite.exists` do the same for the quantifiers: $(\forall a, p(a)) \iff (\forall a, p(\mathrm{op}\ a))$.

The opposite keeps the properties of a type that do not use the product. The instances `MulOpposite.instNontrivial`, `MulOpposite.instInhabited`, `MulOpposite.instSubsingleton`, `MulOpposite.instUnique`, `MulOpposite.instIsEmpty` and `MulOpposite.instDecidableEq` say this.

#### The operations

The module gives each operation of notation on the opposite. The rule is simple: the product reverses, and each other operation stays.

| Lean name | Statement |
|---|---|
| `MulOpposite.op_mul` | $\mathrm{op}(x y) = \mathrm{op}\ y \cdot \mathrm{op}\ x$ |
| `MulOpposite.unop_mul` | $\mathrm{unop}(x y) = \mathrm{unop}\ y \cdot \mathrm{unop}\ x$ |
| `MulOpposite.op_one` | $\mathrm{op}\ 1 = 1$ |
| `MulOpposite.op_inv` | $\mathrm{op}(x^{-1}) = (\mathrm{op}\ x)^{-1}$ |
| `MulOpposite.op_add` | $\mathrm{op}(x + y) = \mathrm{op}\ x + \mathrm{op}\ y$ |
| `MulOpposite.op_sub` | $\mathrm{op}(x - y) = \mathrm{op}\ x - \mathrm{op}\ y$ |
| `MulOpposite.op_zero` | $\mathrm{op}\ 0 = 0$ |
| `MulOpposite.op_smul` | $\mathrm{op}(a \cdot b) = a \cdot \mathrm{op}\ b$ |
| `MulOpposite.op_eq_one_iff` | $\mathrm{op}\ a = 1 \iff a = 1$ |
| `MulOpposite.op_eq_zero_iff` | $\mathrm{op}\ a = 0 \iff a = 0$ |

Each lemma holds by definition, because the instance `MulOpposite.instMul` defines the product of $x$ and $y$ as $\mathrm{op}(\mathrm{unop}\ y \cdot \mathrm{unop}\ x)$. The additive opposite has the dual table: `AddOpposite.op_add` reverses the sum, and `AddOpposite.op_mul` keeps the product.

The scalar action `MulOpposite.instSMul` lets $\alpha$ act on the opposite of $\beta$ through the action on $\beta$. Do not confuse it with the right action of a monoid on itself. A right action of $M$ on $\beta$ is a left action of the opposite of $M$, and Mathlib writes right actions in this form.

The module `Mathlib.Algebra.Opposites` stops at the operations. The instances of monoid and group, such as `MulOpposite.instMonoid` and `MulOpposite.instGroup`, and the lemma `MulOpposite.op_pow`, are in the module `Mathlib.Algebra.Group.Opposite`. For a commutative monoid, `MulOpposite.opMulEquiv` is an isomorphism of a monoid with its opposite. For a group, the inverse map is an isomorphism of $G$ with its opposite, because $(xy)^{-1} = y^{-1} x^{-1}$. This is `MulEquiv.inv'`.

The proof that the opposite of a monoid is a monoid shows why the opposite is useful. Associativity in the opposite is $(a * b) * c = c (b a)$ and $a * (b * c) = (c b) a$. These are equal by associativity in $M$. The unit laws exchange: the left unit law in the opposite is the right unit law in $M$.

#### The symmetrized algebra

Let $A$ be an algebra over a ring in which $2$ is invertible. The symmetrized product on $A$ is

$$a \circ b = \tfrac12 (a b + b a).$$

It is commutative, but in general not associative. The type `SymAlg` of $A$ has the same elements as $A$ and this product. Its two maps are equivalences: `SymAlg.sym` from $A$ to the new type and `SymAlg.unsym` back, with `SymAlg.unsym_sym` and `SymAlg.sym_unsym`. Unlike `MulOpposite`, the type `SymAlg` is a plain definition equal to $A$, so the two maps are the identity equivalence.

The additive structure stays. The lemmas `SymAlg.sym_add`, `SymAlg.sym_sub`, `SymAlg.sym_neg`, `SymAlg.sym_zero`, `SymAlg.sym_one`, `SymAlg.sym_inv` and `SymAlg.sym_smul` say that the map commutes with these operations. The instances `SymAlg.addCommGroup` and `SymAlg.instModule` give the additive group and the module.

The product changes. The instance of the product needs a one, an addition, a numeral $2$ and an instance `Invertible` of $2$. Its two forms are:

| Lean name | Statement |
|---|---|
| `SymAlg.mul_def` | $a \circ b = \mathrm{sym}(\tfrac12(\mathrm{unsym}\ a \cdot \mathrm{unsym}\ b + \mathrm{unsym}\ b \cdot \mathrm{unsym}\ a))$ |
| `SymAlg.sym_mul_sym` | $\mathrm{sym}\ a \circ \mathrm{sym}\ b = \mathrm{sym}(\tfrac12(a b + b a))$ |
| `SymAlg.unsym_mul` | $\mathrm{unsym}(a \circ b) = \tfrac12(\mathrm{unsym}\ a \cdot \mathrm{unsym}\ b + \mathrm{unsym}\ b \cdot \mathrm{unsym}\ a)$ |
| `SymAlg.mul_comm` | $a \circ b = b \circ a$ |
| `SymAlg.sym_mul_self` | $\mathrm{sym}(a a) = \mathrm{sym}\ a \circ \mathrm{sym}\ a$ |
| `SymAlg.invOf_sym` | the inverse of $\mathrm{sym}\ a$ is $\mathrm{sym}$ of the inverse of $a$ |

The proof of `SymAlg.mul_comm` is the commutativity of the sum: $ab + ba = ba + ab$. The proof of `SymAlg.sym_mul_self` is $\frac12(a a + a a) = \frac12 \cdot 2 a^2 = a^2$, and it uses that $2$ is invertible.

For a semiring $A$, the instance `SymAlg.nonAssocSemiring` makes the symmetrized type a semiring without associativity. The distributive laws follow from the distributive laws of $A$. For a ring, `SymAlg.instNonAssocRingOfInvertibleOfNat` gives a ring without associativity, and `SymAlg.instCommMagmaOfInvertibleOfNat` records the commutativity.

#### The Jordan identity

A commutative magma $J$ is a commutative Jordan algebra when

$$(a b)(a a) = a (b (a a))$$

for all $a$ and $b$. This is the class `IsCommJordan`, with the field `IsCommJordan.lmul_comm_rmul_rmul`. The instance `SymAlg.instIsCommJordan` says that the symmetrized algebra of a ring with $2$ invertible is a commutative Jordan algebra.

Here is the computation. Put $c = a \circ a$, which is $a^2$ by `SymAlg.sym_mul_self`. Expand both sides with the definition of $\circ$:

$$a \circ (b \circ c) = \tfrac14 (a b c + a c b + b c a + c b a), \qquad (a \circ b) \circ c = \tfrac14 (a b c + b a c + c a b + c b a).$$

The difference of the two sides is $\frac14 (a c b + b c a - b a c - c a b)$. Now $c = a^2$ commutes with $a$, so $a c b = a^3 b = c a b$ and $b c a = b a^3 = b a c$. So the difference is $0$. The proof in Mathlib does the same expansion with ring arithmetic. The self-adjoint operators on a Hilbert space are the main example: they are closed under $\circ$ but not under the product.

The module `Mathlib.Algebra.Group.Opposite` gives the opposite each structure of the hierarchy. The instances `MulOpposite.instMonoid`, `MulOpposite.instGroup` and `MulOpposite.instCommGroup` are examples. Left and right exchange: a right cancellative monoid has a left cancellative opposite, by `MulOpposite.instLeftCancelMonoid`. The additive structure of $\alpha$ passes to $\alpha^{\mathrm{op}}$ unchanged, by `MulOpposite.instAddCommGroup`. The maps respect powers, by `MulOpposite.op_pow` and `MulOpposite.op_zpow`, but division reverses: `MulOpposite.op_div` states $\operatorname{op}(x / y) = \operatorname{op}(y)^{-1} \operatorname{op}(x)$. Commuting pairs stay commuting, by `MulOpposite.commute_op`, and `SemiconjBy.op` reverses the roles in a semiconjugacy. The same module gives the additive opposite `AddOpposite` its structures, for example `AddOpposite.instAddGroup`.

The module `Mathlib.Algebra.Group.Equiv.Opposite` treats the maps. A homomorphism $f : M \to N$ gives a homomorphism of the opposites, by the equivalence `MonoidHom.op`, with inverse `MonoidHom.unop`. An isomorphism gives an isomorphism of the opposites, by `MulEquiv.op`. The double opposite is the original monoid, by `MulEquiv.opOp`. In a division monoid the inverse is an isomorphism `MulEquiv.inv' G : G ≃* Gᵐᵒᵖ`, since $(a b)^{-1} = b^{-1} a^{-1}$. In a commutative monoid, `MulOpposite.opMulEquiv` makes `MulOpposite.op` itself an isomorphism. A homomorphism with commuting values factors through the opposite, by `MonoidHom.toOpposite` and `MonoidHom.fromOpposite`.

#### Common errors

1. `MulOpposite.op_mul` reverses the factors. A rewrite with it changes $\mathrm{op}(x y)$ to $\mathrm{op}\ y \cdot \mathrm{op}\ x$, not to $\mathrm{op}\ x \cdot \mathrm{op}\ y$. The additive opposite reverses sums, and `MulOpposite.op_add` keeps the order of a sum.
2. The group structure on the opposite is not in `Mathlib.Algebra.Opposites`. A file that needs the instance of group on the opposite must import `Mathlib.Algebra.Group.Opposite`.
3. `SymAlg` needs an instance `Invertible` of $2$. Over a ring of characteristic $2$ the product is not defined, and the instance search fails with a missing instance of `Invertible`.

### Exercises

1. (A) Let $M$ be a commutative semigroup. Prove that $\mathrm{op}(x y) = \mathrm{op}\ x \cdot \mathrm{op}\ y$ for all $x$ and $y$, with `MulOpposite.op_mul` and `MulOpposite.op_injective`.
2. (A) Show with `MulOpposite.rec'` that each element of the opposite of $\alpha$ is $\mathrm{op}\ x$ for exactly one $x$ in $\alpha$.
3. (B) Let $G$ be a group. Prove that $x \mapsto \mathrm{op}(x^{-1})$ is an isomorphism of $G$ with its opposite, and compare with `MulEquiv.inv'`.
4. (B) In the symmetrized algebra of the $2 \times 2$ real matrices, find $a$, $b$ and $c$ with $(a \circ b) \circ c \ne a \circ (b \circ c)$.
5. (B) Prove that in the symmetrized algebra of a commutative ring with $2$ invertible, the product is the product of the ring.
6. (C) Let $A$ be a ring with $2$ invertible. Prove that a subset of $A$ closed under addition, under $x \mapsto \frac12 x$ and under $x \mapsto x^2$ is closed under $\circ$.

### Reference

<?reference?>
