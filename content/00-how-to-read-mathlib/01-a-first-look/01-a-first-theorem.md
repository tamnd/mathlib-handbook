---
title: A first theorem
kind: guide
modules: []
explains: {}
families: []
requires: []
reads_with: ["MIL Ch. 1", "TPIL"]
lean:
  - MathlibHandbook/V00/C01/Examples.lean
  - MathlibHandbook/V00/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## A first theorem

### Overview

Mathlib is the library of mathematics for the Lean prover. At the Mathlib commit of this edition, it has 342,368 declarations, and 253,531 of them are theorems. The topics go from the natural numbers to schemes and manifolds. Each theorem in Mathlib has a proof, and the Lean kernel checks each step of that proof. A theorem in Mathlib is therefore as reliable as the small kernel that checks it.

This section shows a first theorem of algebra in the form that Lean gives it. It reads the theorem symbol by symbol, it proves the same theorem on paper from the axioms, and it shows what the tactic that proves it in Lean does. It then shows the editor view that a reader uses to follow a proof, and the companion package that holds every Lean example of the handbook. After this section the reader can open a Lean file, read a short statement, and run it.

### The square of a sum

Start with the mathematics. A *commutative semiring* is a set $R$ with two operations $+$ and $\cdot$ and two elements $0$ and $1$, such that $(R, +, 0)$ is a commutative monoid, $(R, \cdot, 1)$ is a commutative monoid, multiplication distributes over addition, and $0 \cdot a = a \cdot 0 = 0$ for each $a$. A commutative ring is a commutative semiring in which each element has an additive inverse. The natural numbers $\mathbb{N}$ form a commutative semiring but not a ring. The integers, the rationals and the reals form commutative rings. In a semiring, the element $2$ means $1 + 1$, and $a^2$ means $a \cdot a$.

**Theorem (The square of a sum).** Let $R$ be a commutative semiring and let $a, b \in R$. Then $(a + b)^2 = a^2 + 2ab + b^2$.

*Proof.* By the definition of the square, $(a+b)^2 = (a+b)(a+b)$. Distributivity on the left gives $(a+b)(a+b) = a(a+b) + b(a+b)$. Distributivity on the right, used twice, gives $a(a+b) = a^2 + ab$ and $b(a+b) = ba + b^2$. So $(a+b)^2 = (a^2 + ab) + (ba + b^2)$. Multiplication is commutative, so $ba = ab$. Addition is associative, so the sum is $a^2 + (ab + ab) + b^2$. Finally $ab + ab = 1 \cdot ab + 1 \cdot ab = (1 + 1) ab = 2ab$ by distributivity, and $2ab = (2a)b$ by associativity of multiplication. This gives $(a+b)^2 = a^2 + 2ab + b^2$. $\square$

The proof uses only the axioms of a commutative semiring. It uses no subtraction and no division. So the identity is true in $\mathbb{N}$, in $\mathbb{Z}$, in $\mathbb{R}$, in the ring of polynomials $\mathbb{Z}[x]$ and in each other commutative semiring.

### The theorem in Lean

In Lean, the statement for the integers is one line of text, and the proof is one word.

**Example (The square of a sum).** The tactic `ring` proves each identity of commutative rings and commutative semirings.

<?lean MathlibHandbook/V00/C01/Examples.lean#add_sq?>

Read the block from left to right.

1. The text between `/--` and `-/` is the documentation string of the declaration. Lean keeps it, and the documentation pages show it.
2. The keyword `theorem` starts a declaration whose value is a proof.
3. The name `add_sq_example` is the name of the declaration. The full name is `MathlibHandbook.V00.C01.add_sq_example`, because the file opens the namespace `MathlibHandbook.V00.C01`.
4. The part `(a b : ℤ)` gives two variables $a$ and $b$ of type `ℤ`, the integers. The colon reads "of type" or "in".
5. The part after the next colon is the statement. The symbol `^` is the power, and `*` is the multiplication. Lean needs the symbol `*`: the text `2ab` is not a product.
6. The symbol `:=` starts the proof.
7. The word `by` starts a proof by tactics, and `ring` is the only tactic of the proof.

The statement reads, in words: for all integers $a$ and $b$, $(a+b)^2 = a^2 + 2 \cdot a \cdot b + b^2$. The product `2 * a * b` means `(2 * a) * b`, because `*` groups to the left. In the same way `a + b + c` means `(a + b) + c`.

### What the tactic ring does

A tactic is a program that builds a proof. The tactic `ring` works in any commutative semiring. It reads the two sides of the goal as polynomials in the atoms $a$ and $b$. It brings each side to a normal form: it expands each product, it sorts the monomials in a fixed order, and it collects the coefficients. Here both sides have the normal form $a^2 + 2ab + b^2$, so the two sides are equal. The tactic then builds a proof term from the axioms of a commutative semiring, the same axioms that the proof on paper uses. The kernel checks that term. The reader does not see the term, but it exists, and Chapter 3 shows how to look at such terms.

The tactic `ring` does not use any hypothesis of the context. It proves only identities that are true in every commutative semiring. It fails on the statement $a^2 = 4$ with the hypothesis $a = 2$, because that statement is not an identity. Chapter 3 shows the tactics that use hypotheses.

::: mathlib
`add_sq` · `Mathlib.Algebra.Ring.Defs`

Mathlib has the identity of this section as the lemma `add_sq`. The lemma is stated for each commutative semiring, so it applies to `ℕ` as well as to `ℤ`, `ℚ` and `ℝ`. The type `α` and the structure of semiring are arguments that Lean fills in from the terms `a` and `b`. Chapter 2 explains how to read this line. The example above proves the identity again with `ring` only to show the tactic. In a real proof, the term `add_sq a b` is a proof of the same statement.

<?decl add_sq?>
:::

### A second example: an inequality

The tactic `positivity` proves goals of the form $0 \le e$ and $0 < e$. It looks at the form of the expression $e$: a square is not negative, a sum of nonnegative terms is not negative, a product of positive terms is positive, and so on.

**Example (A sum of squares).** The statement $0 \le a^2 + b^2$ is true in each ordered field.

<?lean MathlibHandbook/V00/C01/Examples.lean#sq_nonneg_sum?>

The type `ℚ` is the field of rational numbers. Here is the proof on paper. It is the proof that `positivity` follows.

**Theorem (Squares are not negative).** Let $F$ be an ordered field and let $a, b \in F$. Then $0 \le a^2$, and $0 \le a^2 + b^2$.

*Proof.* The order of $F$ is total, so $0 \le a$ or $a < 0$. If $0 \le a$, then $0 \le a \cdot a$, because the product of two nonnegative elements is nonnegative in an ordered field. If $a < 0$, then $0 < -a$, and $a \cdot a = (-a)(-a)$ by the rule $(-x)(-y) = xy$ of rings. The right side is the product of two positive elements, so it is positive, and so $0 \le a^2$. The same argument gives $0 \le b^2$. In an ordered field, $0 \le x$ and $0 \le y$ give $0 = 0 + 0 \le x + 0 \le x + y$, by two uses of the rule that adding an element keeps the order. So $0 \le a^2 + b^2$. $\square$

::: mathlib
`sq_nonneg` · `Mathlib.Algebra.Order.Ring.Unbundled.Basic`

The lemma `sq_nonneg` states $0 \le a^2$. Its signature lists several conditions in square brackets: a semiring, a linear order, and three order conditions with the names `ExistsAddOfLE`, `PosMulMono` and `AddLeftMono`. Each ordered field satisfies them, and so does `ℕ`. Mathlib states the lemma with the weakest conditions that the proof needs. Section 2.2 explains these conditions.

<?decl sq_nonneg?>
:::

The module in the first line of a Mathlib box is the file of Mathlib that has the declaration. Section 1.2 explains modules.

### A worked computation: the same statement in ℕ

The tactic `ring` proves the identity $(a - b)^2 = a^2 - 2ab + b^2$ in `ℤ`. The same text with `(a b : ℕ)` is false. Subtraction on `ℕ` stops at zero: in Mathlib, $m - n = 0$ when $m < n$. Take $a = 1$ and $b = 3$.

- The left side: $1 - 3 = 0$ in `ℕ`, so $(1 - 3)^2 = 0^2 = 0$.
- The right side: Lean reads `a ^ 2 - 2 * a * b + b ^ 2` as `(a ^ 2 - 2 * a * b) + b ^ 2`. Here $a^2 = 1$ and $2ab = 6$, so $a^2 - 2ab = 1 - 6 = 0$ in `ℕ`. Then the right side is $0 + 9 = 9$.

So the two sides are $0$ and $9$, and the statement is false in `ℕ`. The tactic `ring` fails on it, and it is right to fail. This is the first junk value of the handbook. Section 5.1 explains junk values in full.

### The editor and the goal view

A Lean file is read in an editor with the Lean extension, usually Visual Studio Code. The editor runs Lean on the file as the reader types. A panel beside the text, the *infoview*, shows the state of the proof at the cursor. When the cursor is after `by` in the first example, the infoview shows the goal:

```text
a b : ℤ
⊢ (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2
```

The lines above the symbol `⊢` are the context: the variables and the hypotheses that the proof can use. The line after `⊢` is the goal, the statement that is still to prove. When the cursor is after `ring`, the infoview shows `No goals`: the proof is complete. A reader of a proof in Mathlib moves the cursor from line to line and reads the goal at each step. Section 3.2 does this for longer proofs.

The editor also shows errors. A red line under a tactic means that the tactic failed. The message says why, for example `ring failed` with the goal that remains. A yellow line means a warning. A proof that uses `sorry` gives the warning `declaration uses 'sorry'`: the word `sorry` closes any goal without a proof, so the theorem is not proved.

### The companion package

Each Lean block of the handbook is in the package `MathlibHandbook` of the repository tamnd/mathlib-lean. The examples of Volume $n$, Chapter $m$ are in the file `MathlibHandbook/V<n>/C<m>/Examples.lean`. Each example has an anchor, a comment `-- anchor: name` before it and `-- end: name` after it, and the handbook cuts the example out by its anchor. The build of the package checks each example, so each block in a book is correct for the Mathlib commit of the edition. The exercises in Lean are in `Exercises.lean`, with `sorry` in place of each proof. The file `Solutions.lean` has the same statements with complete proofs.

To work with the examples, install Lean with `elan`, clone the repository and run `lake exe cache get`, then `lake build`. The command `lake exe cache get` downloads the compiled files of Mathlib, so the first build takes minutes and not hours. Then open the folder in the editor and open a file of the package.

### Common errors

1. Writing `2a` or `ab` for a product. Lean reads `ab` as one name. Write `2 * a` and `a * b`.
2. Forgetting the type of a numeral. In `example : 2 / 3 = 0`, the numerals are natural numbers by default, and the statement is true because division in `ℕ` rounds down. Write `(2 : ℚ) / 3` for the rational number.
3. Reading `a - b` in `ℕ` as the usual difference. It is the usual difference only when $b \le a$.
4. Using `ring` for a statement that needs a hypothesis. Use `linarith`, `nlinarith` or a rewrite first, as Section 3.2 shows.

### Exercises

1. (A) Write the statement of `add_sq_example` for the real numbers. Which part of the block changes?
2. (A) The tactic `ring` proves $(a - b)^2 = a^2 - 2ab + b^2$ in `ℤ`. Explain why it cannot prove this identity in `ℕ` with the same statement. Give a pair $(a, b)$ other than $(1, 3)$ for which the two sides differ in `ℕ`.
3. (A) Prove on paper, from the axioms of a commutative ring, that $(a + b)(a - b) = a^2 - b^2$. Mark each axiom that the proof uses.
4. (B) Find natural numbers $a$ and $b$ for which $(a - b)^2 = a^2 - 2ab + b^2$ is true in `ℕ`, and prove that it is true for all $a, b$ with $b \le a$. Hint: write $a = b + c$.
5. (B) The tactic `positivity` proves $0 < a^2 + 1$ in `ℚ`. Write the proof on paper. Explain why it cannot prove $0 < a^2$.
6. (L) Prove `MathlibHandbook.V00.C01.Exercises.sub_sq_example` in the file `MathlibHandbook/V00/C01/Exercises.lean`.
7. (L) Prove `MathlibHandbook.V00.C01.Exercises.sq_add_one_pos`: for each rational number $a$, $0 < a^2 + 1$.

### Notes and history

Mathlib started in 2017 as the mathematics library of Lean 3. The community moved it to Lean 4 from 2021 to 2023, with an automatic translation followed by years of manual work. The library has hundreds of authors, and each file names its authors in its first lines. The tactic `ring` of Mathlib follows the method of Grégoire and Mahboubi (2005) for the Coq prover: normalize both sides of an equation as polynomials and compare the normal forms. The book *Mathematics in Lean* by Avigad and Massot is the standard first text for Mathlib, and its Chapter 1 and Chapter 2 are good companions to this chapter.
