# Binary numerals and positive naturals

The type `ℕ` of Chapter 1 is a unary type: its elements are built from `0` and the successor. This chapter shows the other forms of the natural numbers in Mathlib. The bits of a number, the binary types `PosNum`, `Num` and `ZNum`, and the type `ℕ+` of positive natural numbers all describe the same numbers with another structure, and each comes with casts and equivalences to `ℕ` or `ℤ`.

The first section gives the bits of a natural number: the constructor `Nat.bit`, binary recursion, the bitwise operations and the length in bits. The second section gives the binary types `PosNum`, `Num` and `ZNum`, their casts to `ℕ` and `ℤ`, and the lemmas that transfer each operation along these casts. The third section gives the type `ℕ+`, its conversions from `ℕ`, its special subtraction and remainder, and the multiset of prime factors of a positive number.
