/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Data

/-!
# M11 coset certificate: Eligibility

The checker's exact word-eligibility condition and an empty-word point.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

/-- The original checker's relator-or-subgroup eligibility condition. -/
@[expose]
def eligible (c : Fin 990 × List (Fin 4)) : Bool :=
  c.2 ∈ relators || (table.word c.1 = [] && c.2 ∈ subgroupWords)

theorem root_word : table.word p0 = [] := by rfl

theorem has_root : (List.finRange 990).any (fun i ↦ table.word i = []) = true := by
  apply List.any_eq_true.mpr
  exact ⟨p0, by simp, by simp only [root_word, decide_true]⟩

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
