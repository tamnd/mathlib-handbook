# Limit theorems

The limit theorems describe the sum $S_n = X_1 + \cdots + X_n$ of many independent variables. They are the first deep results of probability, and the reason that averages of measurements are reliable. The laws of large numbers say that $S_n/n$ converges to the mean. The central limit theorem says that the fluctuation $S_n - nm$ has the size $\sqrt{n}$ and a Gaussian shape.

Section 1 defines almost sure convergence, convergence in probability and convergence in $L^p$, proves the weak law with Chebyshev's inequality, and proves the strong law in Etemadi's form, which needs only pairwise independence. Its examples are Borel's theorem on normal numbers and Monte Carlo integration. Section 2 defines convergence in distribution, connects it with characteristic functions through the Lévy continuity theorem, proves the central limit theorem, and gives the Cramér-Wold device for the multivariate case. Its main example is the theorem of de Moivre and Laplace for coin tosses, with a numerical value.

The chapter needs Chapters 1 to 4, and Volume 18, Measure and integration, for the modes of convergence, Vitali's theorem and the weak convergence of measures. Mathlib has the strong law in `Mathlib.Probability.StrongLaw` and the central limit theorem in `Mathlib.Probability.CentralLimitTheorem`.
