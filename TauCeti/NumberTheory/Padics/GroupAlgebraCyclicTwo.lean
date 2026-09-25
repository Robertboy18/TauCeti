/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.Algebra.MonoidAlgebra.CyclicTwo

/-!
# The dyadic group ring `ℤ₂[C₂]` and its splitting over `ℚ₂`

For `C₂ = Multiplicative (ZMod 2)` with generator `σ`, the group ring `ℚ₂[C₂]` splits as
`ℚ₂ × ℚ₂` through the idempotents `(1 ± σ)/2`, the two eigenspaces of the involution `σ`. Over
`ℤ₂` those idempotents are not available, because `2` is not a unit of `ℤ₂`, and there is no
integral splitting: the only idempotents of `ℤ₂[C₂]` are `0` and `1`.

These are the two facts about the coefficient ring `ℤ₂[C₂]` of the completed group algebra
`ℤ₂[[C₂ × ℤ₂]] ≅ ℤ₂[C₂][[T]]` that Labute's treatment of the even-rank Demushkin groups with
`q = 2` and orientation image `{±1} × U^(f)` relies on: basis corrections are read in the two
`ℚ₂`-eigenspaces and then cleared of denominators, and no direct-product decomposition over
`ℤ₂` is available.

## Main declarations

* `TauCeti.monoidAlgebraRatPadicCyclicTwoEquiv`: `ℚ₂[C₂] ≃ₐ[ℚ₂] ℚ₂ × ℚ₂`.
* `TauCeti.monoidAlgebraPadicIntCyclicTwo_isIdempotentElem_iff`: the idempotents of `ℤ₂[C₂]`
  are exactly `0` and `1`.

## References

J. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §4, p. 122.
-/

public section

namespace TauCeti

/-- Over `ℚ₂`, the idempotents `(1 ± σ)/2` split the group ring of `C₂` into the two eigenspaces
of `σ`: `ℚ₂[C₂] ≃ₐ[ℚ₂] ℚ₂ × ℚ₂`. This is `MonoidAlgebra.cyclicTwoEquivProd` for the
field `ℚ₂`, in which `2` is invertible. -/
noncomputable def monoidAlgebraRatPadicCyclicTwoEquiv :
    MonoidAlgebra ℚ_[2] (Multiplicative (ZMod 2)) ≃ₐ[ℚ_[2]] ℚ_[2] × ℚ_[2] :=
  letI : Invertible (2 : ℚ_[2]) := invertibleOfNonzero two_ne_zero
  MonoidAlgebra.cyclicTwoEquivProd ℚ_[2]

/-- The dyadic splitting sends `a + bσ` to `(a + b, a - b)`, where `a` and `b` are the
coefficients at `1` and at the generator `σ`. -/
@[simp]
theorem monoidAlgebraRatPadicCyclicTwoEquiv_apply
    (x : MonoidAlgebra ℚ_[2] (Multiplicative (ZMod 2))) :
    monoidAlgebraRatPadicCyclicTwoEquiv x =
      (x.coeff 1 + x.coeff (Multiplicative.ofAdd 1),
        x.coeff 1 - x.coeff (Multiplicative.ofAdd 1)) := by
  let : Invertible (2 : ℚ_[2]) := invertibleOfNonzero two_ne_zero
  change MonoidAlgebra.cyclicTwoEquivProd ℚ_[2] x = _
  rw [MonoidAlgebra.cyclicTwoEquivProd_apply]
  simpa only [MonoidAlgebra.cyclicTwoToProd_single_one_add_single_ofAdd_one] using
    congrArg (MonoidAlgebra.cyclicTwoToProd ℚ_[2])
      (MonoidAlgebra.eq_single_one_add_single_ofAdd_one x)

/-- The inverse dyadic splitting sends `(x, y)` to `(x + y)/2 + ((x - y)/2) σ`. -/
@[simp]
theorem monoidAlgebraRatPadicCyclicTwoEquiv_symm_apply (z : ℚ_[2] × ℚ_[2]) :
    monoidAlgebraRatPadicCyclicTwoEquiv.symm z =
      MonoidAlgebra.single 1 ((z.1 + z.2) / 2) +
        MonoidAlgebra.single (Multiplicative.ofAdd 1) ((z.1 - z.2) / 2) := by
  let : Invertible (2 : ℚ_[2]) := invertibleOfNonzero two_ne_zero
  change (MonoidAlgebra.cyclicTwoEquivProd ℚ_[2]).symm z = _
  simpa only [invOf_eq_inv, div_eq_mul_inv, mul_comm] using
    MonoidAlgebra.cyclicTwoEquivProd_symm_apply ℚ_[2] z

/-- There is no integral splitting of `ℤ₂[C₂]`: since `2` is not a unit of `ℤ₂`, the idempotents
`(1 ± σ)/2` are not available, and the only idempotents of `ℤ₂[C₂]` are `0` and `1`. -/
@[simp]
theorem monoidAlgebraPadicIntCyclicTwo_isIdempotentElem_iff
    {e : MonoidAlgebra ℤ_[2] (Multiplicative (ZMod 2))} : IsIdempotentElem e ↔ e = 0 ∨ e = 1 :=
  MonoidAlgebra.isIdempotentElem_cyclicTwo_iff ℤ_[2] <| by
    simpa [mem_nonunits_iff] using PadicInt.p_nonunit (p := 2)

end TauCeti
