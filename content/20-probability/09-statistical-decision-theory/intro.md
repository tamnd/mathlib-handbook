# Statistical decision theory

Statistical decision theory studies the choice of an action from random data. A parameter $\theta$ is unknown, the data has a law $P_\theta$ that depends on it, and an estimator turns the data into an estimate. A loss function measures the cost of each estimate, and the risk is the mean loss. The theory compares estimators by their risks.

Mathlib states this theory with the kernels of Chapter 8. The model is a kernel $P$ from the parameter space to the data space, and an estimator is a Markov kernel from the data space to the space of estimates, so randomized estimators are included from the start. Section 1 defines the average risk with respect to a prior, the Bayes risk and the minimax risk, proves the data processing inequality for the Bayes risk, defines the risk increase, and characterizes Bayes estimators through the posterior kernel.

The chapter needs Chapter 8, in particular the composition of kernels and the posterior of Section 2 of Chapter 8, and Volume 18, Measure and integration. In Mathlib, the files are in `Mathlib/Probability/Decision/`.
