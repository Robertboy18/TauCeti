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
an entry `-1`. The final row uses the `-1` entry on its side of the double bond. The
second-to-last row has entry `-2` across that bond, but in rank at least three it also has a
`-1` entry towards the preceding node. The other rows use a neighbouring entry along the
single-bond chain. Rank two is the exception: the long-root row of `B₂` is `(2, -2)`, whose
entries generate only `2ℤ`.

This file names such a neighbour `TauCeti.typeBCartanNeighbor` and packages the resulting
Bezout certificate `TauCeti.typeBCartanBezout`, the integer coefficients `-1` at that neighbour and
`0` elsewhere, whose pairing with the Cartan row is `1`. It says that every simple root of type
`B` in rank at least three is a primitive character of a split torus whose weights are the Cartan
rows. This is the arithmetic hypothesis in
`TauCeti.UniversalEnvelopingAlgebra.kostantTorusSubgroup_le_kostantElementarySubgroup`.

## Main declarations

* `TauCeti.typeBCartanNeighbor`: a node adjacent to a given node with Cartan entry `-1`.
* `TauCeti.cartanMatrixB_typeBCartanNeighbor`: in rank at least three, that Cartan entry is `-1`.
* `TauCeti.typeBCartanBezout` and `TauCeti.sum_cartanMatrixB_mul_typeBCartanBezout`: the explicit
  Bezout certificate for each row of the type-`B` Cartan matrix.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
* `TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generation`.
-/

public section

namespace TauCeti

variable {n : ℕ}

/-- A column index chosen as the successor of `i`, except at the last two indices, where it
is the predecessor. In rank at least three this is an adjacent node of the type-`B` Dynkin
diagram, with Cartan entry `-1` in row `i`. -/
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

/-- Integer coefficients supported at the chosen column: `-1` at `typeBCartanNeighbor n i`
and `0` elsewhere. They certify row primitivity in rank at least three. -/
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
