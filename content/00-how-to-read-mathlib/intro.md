# How to read this handbook

This volume is the guide to the handbook. It is for a reader who knows mathematics and wants to read Mathlib, the library of mathematics for the Lean prover. It does not teach Lean as a programming language. The books *Theorem Proving in Lean 4* and *Mathematics in Lean* do that, and this volume points to them.

The volume has five chapters. Chapter 1 shows a first theorem of Mathlib and the companion package. Chapter 2 shows how to read the signature of a lemma. Chapter 3 shows that a proof is a term, and what the tactics do. Chapter 4 shows how to find a declaration from its statement. Chapter 5 shows the junk values of Mathlib and reads one full proof line by line.

Each Lean block in the handbook comes from the package `MathlibHandbook` of the repository tamnd/mathlib-lean. The build of that package checks each block against the Mathlib commit of the edition. Each name in a block links to its page on mathlib.tamnd.com.

The other volumes have a Mathlib box in each section. The box gives the Lean name of the result, its module and its signature. Chapter 2 of this volume teaches the reader to read that box.
