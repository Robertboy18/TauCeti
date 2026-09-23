/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan

/-!
# Row primitivity of the type-`B` Cartan matrix

In rank at least three, every row of the type-`B` Cartan matrix `CartanMatrix.B (n + 1)` contains
an entry `-1`: each node of the Dynkin diagram is joined by a single bond to a neighbour, since the
double bond `-2` sits only in the row of the second-to-last node, which in rank at least three also
has a neighbour on the other side. Rank two is the exception: the long-root row of `B₂` is
`(2, -2)`, whose entries generate only `2ℤ`.

This file names such a neighbour `TauCeti.typeBCartanNeighbor` and packages the resulting
Bezout certificate `TauCeti.typeBCartanBezout`, the integer coefficients `-1` at that neighbour and
`0` elsewhere, whose pairing with the Cartan row is `1`. It says that every simple root of type
`B` in rank at least three is a primitive character of a split torus whose weights are the Cartan
rows, which is the arithmetic input that the Kostant coroot-generation theorem
`TauCeti.kostantTorusSubgroup_le_kostantElementarySubgroup` requires of a Dynkin type.

## Main declarations

* `TauCeti.typeBCartanNeighbor`: a node adjacent to a given node with Cartan entry `-1`.
* `TauCeti.cartanMatrixB_typeBCartanNeighbor`: in rank at least three, that Cartan entry is `-1`.
* `TauCeti.typeBCartanBezout` and `TauCeti.sum_cartanMatrixB_mul_typeBCartanBezout`: the explicit
  Bezout certificate for each row of the type-`B` Cartan matrix.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
-/

public section

namespace TauCeti

variable {n : ℕ}

/-- A node of the type-`B` Dynkin diagram adjacent to `i`: the successor of `i`, except at the
last two nodes, where it is the predecessor. In rank at least three the Cartan entry of row `i`
at this node is `-1`. -/
def typeBCartanNeighbor (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨if (i : ℕ) + 1 < n then (i : ℕ) + 1 else (i : ℕ) - 1, by split_ifs <;> omega⟩

@[simp]
theorem val_typeBCartanNeighbor (i : Fin (n + 1)) :
    (typeBCartanNeighbor n i : ℕ) = if (i : ℕ) + 1 < n then (i : ℕ) + 1 else (i : ℕ) - 1 :=
  (rfl)

/-- In rank at least three, the type-`B` Cartan matrix has entry `-1` at each node and its
chosen neighbour. -/
theorem cartanMatrixB_typeBCartanNeighbor (hn : 2 ≤ n) (i : Fin (n + 1)) :
    CartanMatrix.B (n + 1) i (typeBCartanNeighbor n i) = -1 := by
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, val_typeBCartanNeighbor]
  split_ifs <;> omega

/-- The Bezout coefficients certifying that row `i` of the type-`B` Cartan matrix is primitive:
`-1` at the neighbour `typeBCartanNeighbor n i` and `0` elsewhere. -/
def typeBCartanBezout (n : ℕ) (i j : Fin (n + 1)) : ℤ :=
  if j = typeBCartanNeighbor n i then -1 else 0

@[simp]
theorem typeBCartanBezout_apply (i j : Fin (n + 1)) :
    typeBCartanBezout n i j = if j = typeBCartanNeighbor n i then -1 else 0 :=
  (rfl)

/-- In rank at least three, every row of the type-`B` Cartan matrix is a primitive integer
vector, with the explicit certificate `typeBCartanBezout`. -/
theorem sum_cartanMatrixB_mul_typeBCartanBezout (hn : 2 ≤ n) (i : Fin (n + 1)) :
    ∑ j, CartanMatrix.B (n + 1) i j * typeBCartanBezout n i j = 1 := by
  rw [Finset.sum_eq_single (typeBCartanNeighbor n i)]
  · simp [cartanMatrixB_typeBCartanNeighbor hn]
  · intro j _ hj
    simp [hj]
  · simp

end TauCeti
