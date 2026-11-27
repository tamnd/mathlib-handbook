# Conditional expectation

Chapter 1 conditions on one event of positive probability. Many questions need more: the conditional law of $Y$ given a continuous variable $X$, where each event $\{X = x\}$ has probability $0$, or the information that is known at a given time in a random process. The conditional expectation $E[X \mid \mathcal{G}]$ with respect to a $\sigma$-algebra answers these questions. It is the basic object of the theory of martingales in Chapter 7.

Section 1 defines the conditional expectation and the conditional variance, lists the properties that Volume 18, Measure and integration, proves, and adds conditioning on an independent $\sigma$-algebra, conditioning on one event, and the law of total variance. Its examples are random sums, with Wald's identity, and the regression of one Gaussian variable on another. Section 2 constructs regular conditional probabilities on standard Borel spaces, shows that conditional expectations are integrals against them, and defines conditional independence. Mathlib defines conditional independence as the independence of Chapter 2 with respect to the kernel of regular conditional probabilities.

The chapter needs Chapters 1 to 5. In Mathlib, `condExp` is in the measure theory part of the library, and the files of this chapter build on it.
