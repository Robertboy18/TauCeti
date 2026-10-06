/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Data
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Subgroup

/-! Exact-group soundness of scan-word rotations and free cancellations. -/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate.RelationSoundness

open Relations

/-- A rotation or inverse rotation of an exact relation is closed. -/
theorem scan_variant_eq_one (r : List (Fin 4)) (w : Word)
    (inverse : Bool) (shift : ℕ) (hw : eval w = 1)
    (heq : decode r = (if inverse then FreeGroup.invRev w else w).rotate shift) :
    (r.map letterValue).prod = 1 := by
  rw [prod_letterValue, heq]
  apply eval_rotate_eq_one
  cases inverse with
  | false => exact hw
  | true =>
    change eval (FreeGroup.invRev w) = 1
    rw [eval_invRev, hw, inv_one]

/-- Free cancellation is checked before mapping to the exact presentation group. -/
theorem scan_reduce_nil (r : List (Fin 4))
    (h : FreeGroup.reduce (decode r) = []) : (r.map letterValue).prod = 1 := by
  rw [prod_letterValue]
  have heq : FreeGroup.mk (decode r) = 1 :=
    FreeGroup.reduce.exact (h.trans FreeGroup.reduce_nil.symm)
  change PresentedGroup.mk _ (FreeGroup.mk (decode r)) = 1
  rw [heq, map_one]

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.RelationSoundness
