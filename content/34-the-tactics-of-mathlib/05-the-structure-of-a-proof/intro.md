# The structure of a proof

This chapter is about the tactics that give a proof its shape. They do no computation. They do the steps that a written proof says with "let", "take", "it is sufficient to show", "there are two cases", "choose", "for large $n$" and "by induction on $n$". The tactics of the earlier chapters close the small goals that these steps leave.

The first section is about `rcases`, `obtain` and `rintro`, which take a hypothesis apart with a pattern. It proves the rules of elimination of `∧`, `∨` and `∃`, and it explains why the witness of an `∃` cannot be taken out inside a definition. The second section is about `choose`, `lift` and `filter_upwards`: the axiom of choice in the form of Lean, the lift of a variable to a smaller type, and the closure of a filter under intersection. The third section is about the first tactics of each proof: `intro`, `exact`, `apply`, `refine`, `constructor`, `use` and `have`, with the goal state and the metavariables. The fourth section is about `induction` and `cases`: the principle of induction with a proof from the well-ordering of $\mathbb{N}$, induction from a base other than $0$, strong induction, and the case splits of `cases`, `rcases` and `interval_cases`.

A reader who is new to Lean can read the third section first. The chapter uses the tactics of Chapters 2 and 3 to close the goals of arithmetic inside the proofs.
