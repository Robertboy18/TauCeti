/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelationSoundness

/-! Finiteness and an upper order bound for the exact M11 presentation. -/

public section

namespace TauCeti.Sporadic.Mathieu

namespace M11CosetCertificate

open Relations

/-- The checked table bounds the index of the cyclic subgroup. -/
theorem index_zpowers_x_le : (Subgroup.zpowers x).index ≤ 990 :=
  CosetTable.index_le closure_range_letterValue check_eq_true
    RelationSoundness.relators_eq_one RelationSoundness.subgroupWords_mem

/-- The checked table proves that the cyclic subgroup has finite index. -/
theorem finiteIndex_zpowers_x : (Subgroup.zpowers x).FiniteIndex :=
  CosetTable.finiteIndex closure_range_letterValue check_eq_true
    RelationSoundness.relators_eq_one RelationSoundness.subgroupWords_mem

end M11CosetCertificate

open M11CosetCertificate M11CosetCertificate.Relations

/-- The exact M11 presentation group is finite. -/
theorem finite_m11Presentation : Finite m11Presentation.Group :=
  (Subgroup.finite_iff_finite_and_finiteIndex (Subgroup.zpowers x)).mpr
    ⟨finite_zpowers_x, finiteIndex_zpowers_x⟩

/-- Its order is at most 990 cosets times at most eight elements in each coset. -/
theorem card_m11Presentation_le : Nat.card m11Presentation.Group ≤ 7920 := by
  rw [← (Subgroup.zpowers x).card_mul_index]
  exact (Nat.mul_le_mul_left _ index_zpowers_x_le).trans
    (Nat.mul_le_mul_right 990 card_zpowers_x_le)

end TauCeti.Sporadic.Mathieu
