# Ordered groups and the absolute value

An ordered group is a group with an order that addition keeps: from $a \le b$ follows $c + a \le c + b$. The integers, the rationals and the reals are ordered groups, and most computations with inequalities use only this axiom.

The first section defines the ordered monoids and the ordered groups through the Mathlib mixins `IsOrderedAddMonoid` and `IsOrderedCancelAddMonoid`. It proves from the axioms that inequalities add, that $a \le b$ exactly when $0 \le b - a$, and that negation reverses the order, and it shows that the positive cone determines the order. The second section defines the absolute value $|a| = a \sqcup (-a)$ and the positive and negative parts, and it proves the triangle inequality, the reverse triangle inequality and the decomposition $a = a^+ - a^-$.

The chapter needs the orders of Chapter 1, the lattices of Chapter 3, and the class hierarchy of Volume 1. The absolute value and the distance $|a - b|$ are the start of the metric spaces and of the estimates of analysis in later volumes.
