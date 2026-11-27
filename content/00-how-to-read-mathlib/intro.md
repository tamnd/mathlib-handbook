# How to read this handbook

This volume is the guide to the handbook. It is for a reader who knows mathematics and wants to read Mathlib, the library of mathematics for the Lean prover. It does not teach Lean as a programming language. The books *Theorem Proving in Lean 4* and *Mathematics in Lean* do that, and this volume points to them. Here the examples are real statements of Mathlib, and each one comes with the mathematics it states and a proof on paper.

The volume has five chapters. Chapter 1 shows a first theorem of Mathlib, the map of the library, and the passage from a statement of a textbook to a statement of Mathlib. Chapter 2 shows how to read the signature of a lemma: the arguments, the type classes, the coercions and the shape of the statement. Chapter 3 shows that a proof is a term, and how to read a tactic proof with its goals. Chapter 4 shows the naming convention, the search tools, and how to read a file of the source. Chapter 5 shows the junk values of Mathlib and reads full proofs line by line.

Read the chapters in order. Each section has exercises graded (A) for a direct check, (B) for a short proof, (C) for a harder proof, and (L) for an exercise in Lean in the companion package. The exercises (A), (B) and (C) need only paper.

Each Lean block with a link in the handbook comes from the package `MathlibHandbook` of the repository tamnd/mathlib-lean. The build of that package checks each such block against the Mathlib commit of the edition. Some sections of this volume also quote the source of Mathlib or show the goal view of an editor. These quotes are marked in the text, and they are for reading, not for the build. Each name in a Mathlib box links to its page on mathlib.tamnd.com.

The other volumes have a Mathlib box in each section. The box gives the Lean name of the result, its module and its signature. Chapter 2 of this volume teaches the reader to read that box.
