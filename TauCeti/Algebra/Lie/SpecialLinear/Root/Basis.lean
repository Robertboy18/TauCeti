/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Finrank
public import TauCeti.Algebra.Lie.SpecialLinear.Diagonal
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod

/-!
# Signed root coordinates for the special linear Lie algebra

Over a commutative ring, adjacent diagonal differences and signed off-diagonal matrix units
form a basis of the trace-zero matrices. Its diagonal coordinates are initial sums; its root
coordinates are signed matrix entries. The construction composes the existing free-entry
equivalence with a partition of its index set and the partial-sum equivalence.
-/

public section

namespace TauCeti

open LieAlgebra.SpecialLinear

variable (r : ℕ) (A : Type*) [CommRing A]

/-- The interval-root sign: positive roots have sign one, and a negative root of height `h`
has sign `(-1) ^ (h - 1)`. -/
def specialLinearRootSign (i j : Fin (r + 1)) : A :=
  if i < j then 1 else (-1) ^ (i.val - j.val - 1)

/-- The sign is determined by the orientation and length of the interval. -/
theorem specialLinearRootSign_eq (i j : Fin (r + 1)) :
    specialLinearRootSign r A i j =
      if i < j then 1 else (-1) ^ (i.val - j.val - 1) := by
  rfl

/-- Every interval-root sign is its own inverse. -/
@[simp]
theorem specialLinearRootSign_mul_self (i j : Fin (r + 1)) :
    specialLinearRootSign r A i j * specialLinearRootSign r A i j = 1 := by
  unfold specialLinearRootSign
  split <;> simp [← mul_pow]

/-- The signed matrix unit belonging to an unequal pair of indices. -/
def specialLinearSignedRoot (i j : Fin (r + 1)) (h : i ≠ j) : sl (Fin (r + 1)) A :=
  single i j h (specialLinearRootSign r A i j)

/-- The underlying matrix of a signed root is its signed matrix unit. -/
@[simp]
theorem specialLinearSignedRoot_val (i j : Fin (r + 1)) (h : i ≠ j) :
    (specialLinearSignedRoot r A i j h).val =
      Matrix.single i j (specialLinearRootSign r A i j) := by
  rfl

private def rootEntryIndexEquiv :
    (Fin r ⊕ {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) ≃
      {p : Fin (r + 1) × Fin (r + 1) // p ≠ (Fin.last r, Fin.last r)} where
  toFun
    | .inl i => ⟨(i.castSucc, i.castSucc), fun h =>
        Fin.castSucc_ne_last i (congrArg Prod.fst h)⟩
    | .inr p => ⟨p.val, fun h =>
        p.property ((congrArg Prod.fst h).trans (congrArg Prod.snd h).symm)⟩
  invFun p := if h : p.val.1 = p.val.2 then
      .inl ⟨p.val.1.val, by
        have hn : p.val.1 ≠ Fin.last r := fun hk =>
          p.property (Prod.ext hk (h.symm.trans hk))
        exact Fin.lt_last_iff_ne_last.mpr hn⟩
    else .inr ⟨p.val, h⟩
  left_inv p := by
    cases p with
    | inl i => simp
    | inr p => simp [p.property]
  right_inv p := by
    dsimp only
    by_cases h : p.val.1 = p.val.2
    · simp only [dite_eq_left h]
      apply Subtype.ext
      exact Prod.ext rfl h
    · simp only [dite_eq_right h]

private def rootSignEquiv :
    ({p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2} → A) ≃ₗ[A]
      ({p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2} → A) where
  toFun d p := specialLinearRootSign r A p.val.1 p.val.2 * d p
  invFun d p := specialLinearRootSign r A p.val.1 p.val.2 * d p
  left_inv d := by
    funext p
    dsimp only
    rw [← mul_assoc, specialLinearRootSign_mul_self, one_mul]
  right_inv d := by
    funext p
    dsimp only
    rw [← mul_assoc, specialLinearRootSign_mul_self, one_mul]
  map_add' d e := by
    ext p
    exact mul_add _ _ _
  map_smul' a d := by
    ext p
    exact mul_left_comm _ _ _

/-- Coordinates on trace-zero matrices adapted to adjacent coroots and signed interval roots. -/
noncomputable def specialLinearRootEquiv :
    sl (Fin (r + 1)) A ≃ₗ[A]
      (Fin r ⊕ {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2} → A) :=
  let split := LinearEquiv.sumArrowLequivProdArrow
    (Fin r) {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2} A A
  (specialLinearEntryEquiv (R := A) (Fin.last r)).trans
    ((LinearEquiv.piCongrLeft' A (fun _ => A) (rootEntryIndexEquiv r).symm).trans
      (split.trans (((partialSumsLinearEquiv A r).prodCongr
        (rootSignEquiv r A)).trans split.symm)))

/-- Coroot coordinates are the nonempty initial sums of diagonal entries. -/
@[simp]
theorem specialLinearRootEquiv_inl (X : sl (Fin (r + 1)) A) (i : Fin r) :
    specialLinearRootEquiv r A X (.inl i) =
      Fin.partialSum (fun j : Fin r => X.val j.castSucc j.castSucc) i.succ := by
  change partialSumsLinearEquiv A r (fun j : Fin r =>
    specialLinearEntryEquiv (R := A) (Fin.last r) X
      ((rootEntryIndexEquiv r) (.inl j))) i = _
  rw [partialSumsLinearEquiv_apply]
  simp_rw [specialLinearEntryEquiv_apply]
  rfl

/-- A root coordinate is the corresponding signed matrix entry. -/
@[simp]
theorem specialLinearRootEquiv_inr (X : sl (Fin (r + 1)) A)
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    specialLinearRootEquiv r A X (.inr p) =
      specialLinearRootSign r A p.val.1 p.val.2 * X.val p.val.1 p.val.2 := by
  change specialLinearRootSign r A p.val.1 p.val.2 *
    specialLinearEntryEquiv (R := A) (Fin.last r) X
      ((rootEntryIndexEquiv r) (.inr p)) = _
  rw [specialLinearEntryEquiv_apply]
  rfl

/-- On diagonal matrices, the new coroot coordinates agree with the existing coordinates. -/
theorem specialLinearRootEquiv_diagonal_inl (X : specialLinearDiagonal r A) (i : Fin r) :
    specialLinearRootEquiv r A X.val (.inl i) = specialLinearCorootEquiv r A X i := by
  rw [specialLinearRootEquiv_inl, specialLinearCorootEquiv_apply]

/-- Diagonal matrices have zero root coordinates. -/
theorem specialLinearRootEquiv_diagonal_inr (X : specialLinearDiagonal r A)
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    specialLinearRootEquiv r A X.val (.inr p) = 0 := by
  rw [specialLinearRootEquiv_inr,
    (mem_specialLinearDiagonal_iff r A X.val).mp X.property p.property, mul_zero]

/-- Adjacent coroots and signed interval roots form a basis over every commutative ring. -/
noncomputable def specialLinearRootBasis :
    Module.Basis (Fin r ⊕ {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) A
      (sl (Fin (r + 1)) A) :=
  Module.Basis.ofEquivFun (specialLinearRootEquiv r A)

/-- The signed root basis has the coordinates given by the full coordinate equivalence. -/
@[simp]
theorem specialLinearRootBasis_repr (X : sl (Fin (r + 1)) A)
    (p : Fin r ⊕ {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    (specialLinearRootBasis r A).repr X p = specialLinearRootEquiv r A X p := by
  exact Module.Basis.ofEquivFun_repr_apply _ _ _

private theorem rootEquiv_basis
    (p : Fin r ⊕ {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    specialLinearRootEquiv r A (specialLinearRootBasis r A p) = Pi.single p 1 := by
  ext q
  rw [← specialLinearRootBasis_repr, Module.Basis.repr_self]
  simp only [Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- The first summand of the full basis is the existing simple-coroot basis. -/
@[simp]
theorem specialLinearRootBasis_inl (i : Fin r) :
    specialLinearRootBasis r A (.inl i) = (specialLinearCorootBasis r A i).val := by
  apply (specialLinearRootEquiv r A).injective
  rw [rootEquiv_basis]
  ext q
  cases q with
  | inl j =>
    rw [specialLinearRootEquiv_diagonal_inl, specialLinearCorootEquiv_apply,
      ← specialLinearCorootBasis_repr, Module.Basis.repr_self]
    simp [Pi.single_apply, Finsupp.single_apply, eq_comm]
  | inr p =>
    rw [specialLinearRootEquiv_diagonal_inr]
    simp

private theorem rootEquiv_signedRoot
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    specialLinearRootEquiv r A
        (specialLinearSignedRoot r A p.val.1 p.val.2 p.property) =
      Pi.single (.inr p) 1 := by
  ext q
  cases q with
  | inl i =>
    rw [specialLinearRootEquiv_inl]
    have hd : (fun j : Fin r =>
        (specialLinearSignedRoot r A p.val.1 p.val.2 p.property).val
          j.castSucc j.castSucc) = 0 := by
      funext j
      rw [specialLinearSignedRoot_val, Matrix.single_apply]
      split
      · rename_i h
        exact False.elim (p.property (h.1.trans h.2.symm))
      · rfl
    rw [hd, ← partialSumsLinearEquiv_apply, map_zero]
    simp
  | inr q =>
    rw [specialLinearRootEquiv_inr, specialLinearSignedRoot_val, Matrix.single_apply]
    by_cases h : p = q
    · subst q
      simp
    · have hp : ¬(p.val.1 = q.val.1 ∧ p.val.2 = q.val.2) := by
        intro hp
        exact h (Subtype.ext (Prod.ext hp.1 hp.2))
      simp [hp, Ne.symm h]

/-- The second summand of the full basis consists of the signed off-diagonal units. -/
@[simp]
theorem specialLinearRootBasis_inr
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    specialLinearRootBasis r A (.inr p) =
      specialLinearSignedRoot r A p.val.1 p.val.2 p.property := by
  apply (specialLinearRootEquiv r A).injective
  rw [rootEquiv_basis, rootEquiv_signedRoot]

end TauCeti
