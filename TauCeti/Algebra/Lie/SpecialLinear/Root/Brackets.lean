/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.Root.Basis
public import TauCeti.Algebra.Lie.GeneralLinear.Basic

/-!
# Brackets of signed special linear root vectors

The two possible endpoint coincidences give the four exhaustive root-bracket cases.
Opposite roots produce a difference of diagonal units; adjacent coroots act by the
difference of their diagonal entries.
-/

public section

namespace TauCeti

open LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable (r : ℕ) (A : Type*) [CommRing A]

/-- Root vectors with no composable endpoints commute. -/
theorem lie_specialLinearSignedRoot_eq_zero
    (i j k l : Fin (r + 1)) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) :
    ⁅specialLinearSignedRoot r A i j hij, specialLinearSignedRoot r A k l hkl⁆ = 0 := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, specialLinearSignedRoot_val, specialLinearSignedRoot_val,
    lie_single_single]
  simp [hjk, hli]

/-- A single forward endpoint coincidence concatenates the two signed roots. -/
theorem lie_specialLinearSignedRoot_of_middle_eq
    (i j l : Fin (r + 1)) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    ⁅specialLinearSignedRoot r A i j hij, specialLinearSignedRoot r A j l hjl⁆ =
      (specialLinearRootSign r A i j * specialLinearRootSign r A j l *
        specialLinearRootSign r A i l) • specialLinearSignedRoot r A i l hil := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, SetLike.val_smul, specialLinearSignedRoot_val,
    specialLinearSignedRoot_val, specialLinearSignedRoot_val, lie_single_single]
  simp [hil.symm, Matrix.smul_single, smul_eq_mul, mul_assoc]

/-- A single reverse endpoint coincidence contributes the negative concatenation. -/
theorem lie_specialLinearSignedRoot_of_outer_eq
    (i j k : Fin (r + 1)) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    ⁅specialLinearSignedRoot r A i j hij, specialLinearSignedRoot r A k i hki⁆ =
      -(specialLinearRootSign r A i j * specialLinearRootSign r A k i *
        specialLinearRootSign r A k j) • specialLinearSignedRoot r A k j hkj := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, SetLike.val_smul, specialLinearSignedRoot_val,
    specialLinearSignedRoot_val, specialLinearSignedRoot_val, lie_single_single]
  simpa [hkj.symm, Matrix.smul_single, smul_eq_mul, mul_assoc] using
    congrArg (fun a : A => -Matrix.single k j a)
      (mul_comm (specialLinearRootSign r A k i) (specialLinearRootSign r A i j))

/-- Opposite signed roots bracket to the corresponding diagonal difference. -/
theorem lie_specialLinearSignedRoot_reverse
    (i j : Fin (r + 1)) (hij : i ≠ j) :
    ⁅specialLinearSignedRoot r A i j hij, specialLinearSignedRoot r A j i hij.symm⁆ =
      (specialLinearRootSign r A i j * specialLinearRootSign r A j i) •
        singleSubSingle i j (1 : A) := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, SetLike.val_smul, specialLinearSignedRoot_val,
    specialLinearSignedRoot_val, val_singleSubSingle, lie_single_single]
  simp [smul_sub, Matrix.smul_single, smul_eq_mul, mul_comm]

/-- A simple coroot acts by the difference of its two diagonal weights. -/
theorem lie_specialLinearCoroot_signedRoot
    (t : Fin r) (i j : Fin (r + 1)) (hij : i ≠ j) :
    ⁅(specialLinearCorootBasis r A t).val, specialLinearSignedRoot r A i j hij⁆ =
      (((if t.castSucc = i then (1 : A) else 0) - (if t.succ = i then 1 else 0)) -
        ((if t.castSucc = j then 1 else 0) - (if t.succ = j then 1 else 0))) •
          specialLinearSignedRoot r A i j hij := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, SetLike.val_smul, specialLinearSignedRoot_val]
  have hd := (mem_specialLinearDiagonal_iff r A _).mp
    (specialLinearCorootBasis r A t).property
  rw [lie_single_of_mem_diagonalCartan (mem_diagonalCartan_iff_isDiag.mpr hd)]
  simp [specialLinearCorootBasis_apply, val_singleSubSingle, Matrix.single_apply]

/-- Simple coroots commute over every coefficient ring. -/
theorem lie_specialLinearCoroot_eq_zero (s t : Fin r) :
    ⁅(specialLinearCorootBasis r A s).val, (specialLinearCorootBasis r A t).val⁆ = 0 := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket]
  exact lie_eq_zero_of_isDiag
    ((mem_specialLinearDiagonal_iff r A _).mp (specialLinearCorootBasis r A s).property)
    ((mem_specialLinearDiagonal_iff r A _).mp (specialLinearCorootBasis r A t).property)

/-- Summing adjacent coroots over an interval gives its endpoint difference. -/
theorem sum_Icc_specialLinearCoroot (i j : Fin r) (hij : i ≤ j) :
    ∑ t ∈ Finset.Icc i j, (specialLinearCorootBasis r A t).val =
      singleSubSingle i.castSucc j.succ (1 : A) := by
  apply Subtype.ext
  -- View the coercion as the additive inclusion so that `map_sum` applies.
  change (sl (Fin (r + 1)) A).incl _ = _
  simp only [map_sum, LieSubalgebra.coe_incl, specialLinearCorootBasis_apply,
    val_singleSubSingle]
  simpa only [neg_sub_neg] using
    (Fin.sum_Icc_sub hij (fun k : Fin (r + 1) ↦ -Matrix.single k k (1 : A)))

/-- Opposite roots on a positive interval bracket to its sum of simple coroots. -/
theorem lie_specialLinearSignedRoot_interval (i j : Fin r) (hij : i ≤ j) :
    ⁅specialLinearSignedRoot r A i.castSucc j.succ
        (show i.castSucc < j.succ from Nat.lt_succ_of_le hij).ne,
      specialLinearSignedRoot r A j.succ i.castSucc
        (show i.castSucc < j.succ from Nat.lt_succ_of_le hij).ne'⁆ =
      (specialLinearRootSign r A i.castSucc j.succ *
        specialLinearRootSign r A j.succ i.castSucc) •
          ∑ t ∈ Finset.Icc i j, (specialLinearCorootBasis r A t).val := by
  rw [lie_specialLinearSignedRoot_reverse, sum_Icc_specialLinearCoroot r A i j hij]

/-- Reversing the two roots negates the interval-coroot expansion. -/
theorem lie_specialLinearSignedRoot_interval_reverse (i j : Fin r) (hij : i ≤ j) :
    ⁅specialLinearSignedRoot r A j.succ i.castSucc
        (show i.castSucc < j.succ from Nat.lt_succ_of_le hij).ne',
      specialLinearSignedRoot r A i.castSucc j.succ
        (show i.castSucc < j.succ from Nat.lt_succ_of_le hij).ne⁆ =
      -(specialLinearRootSign r A i.castSucc j.succ *
        specialLinearRootSign r A j.succ i.castSucc) •
          ∑ t ∈ Finset.Icc i j, (specialLinearCorootBasis r A t).val := by
  rw [← lie_skew, lie_specialLinearSignedRoot_interval r A i j hij, neg_smul]

end TauCeti
