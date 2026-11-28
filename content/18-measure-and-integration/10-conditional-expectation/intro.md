# Conditional expectation

This chapter studies the conditional expectation of a function with respect to a smaller σ-algebra. The conditional expectation is the function that is measurable for the smaller σ-algebra and has the same integral as the original function over each of its sets. It is the base of martingales and conditional laws in probability.

Section 1 constructs the conditional expectation. Mathlib defines it first on $L^2$ as an orthogonal projection, extends it to $L^1$ by continuity and then to integrable functions with values in a complete normed space. The section also gives the lemmas that identify a function from its integrals over measurable sets. Section 2 gives the properties that proofs use: locality on sets, pulling out a known factor, the contraction of $L^p$ norms, the conditional inequality of Jensen and the relation with the theorem of Radon and Nikodym. It ends with the conditional expectation of functions with values in $[0, \infty]$.

The chapter needs the measures of Chapter 2, the integrals of Chapters 4 and 5 and the spaces $L^p$ of Chapter 7. The martingales of Volume 20 use the results of this chapter.
