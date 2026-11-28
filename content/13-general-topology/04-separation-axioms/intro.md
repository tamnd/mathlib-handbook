# Separation axioms

The axioms of a topology permit spaces with few open sets, such as the indiscrete space, in which a sequence tends to each point. The separation axioms ask for enough open sets to tell points, or points and closed sets, or two closed sets, apart. Each axiom has a name of the form $T_i$, after the German word *Trennungsaxiom*.

Section 1 studies the axioms for points: $T_0$, $T_1$ and the Hausdorff axiom $T_2$. In a Hausdorff space a filter has at most one limit, and so Mathlib can define "the limit". Section 2 studies regular and normal spaces, where closed sets are separated from points and from each other. It proves that each metric space is normal. Chapter 5 proves that each compact Hausdorff space is normal, and Chapter 8 shows what normality gives: the lemma of Urysohn and the theorem of Tietze. Section 3 describes the library of the specialization relation, inseparable points and the Kolmogorov quotient, which make sense in each space, also without $T_0$.

The chapter needs Chapters 1 to 3. The filter form of the Hausdorff axiom, disjoint neighbourhood filters, uses the order on filters of Chapter 2.
