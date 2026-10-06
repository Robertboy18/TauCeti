/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Endpoints
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Transitions00
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Transitions01
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Transitions02
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Transitions03
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Transitions04
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Transitions05
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Transitions06
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Transitions07
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Transitions08
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Transitions09
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Transitions10
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Transitions11

/-!
# Acceptance of the 990-point M11 coset certificate

`checkFast_eq_true` and `check_eq_true` verify the concrete table, its 632 scan words,
the two subgroup words and all 2971 deductions. Sixteen initial checks identify
the tree edges; 93 successive transitions end with all 3960 edges known.
Bit-mask simulation relates these computations to the original checker.

These theorems establish Boolean acceptance. Interpreting the words in the exact
presented M11 group and proving their relator or subgroup membership are separate
inputs to `CosetTable.finiteIndex` and `CosetTable.index_le`.
This supplies the concrete certificate prerequisite for milestones P0 and P1 of
`TauCetiRoadmap/CFSGBasicProperties/README.md`.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

/-- Every deduction uses a permitted word at a permitted point. -/
theorem all_eligible : deductions.all eligible = true := by
  simp only [deductions, List.append_eq, List.all_append, eligible000, eligible001, eligible002,
    eligible003, eligible004, eligible005, eligible006, eligible007, eligible008, eligible009,
    eligible010, eligible011, eligible012, eligible013, eligible014, eligible015, eligible016,
    eligible017, eligible018, eligible019, eligible020, eligible021, eligible022, eligible023,
    eligible024, eligible025, eligible026, eligible027, eligible028, eligible029, eligible030,
    eligible031, eligible032, eligible033, eligible034, eligible035, eligible036, eligible037,
    eligible038, eligible039, eligible040, eligible041, eligible042, eligible043, eligible044,
    eligible045, eligible046, eligible047, eligible048, eligible049, eligible050, eligible051,
    eligible052, eligible053, eligible054, eligible055, eligible056, eligible057, eligible058,
    eligible059, eligible060, eligible061, eligible062, eligible063, eligible064, eligible065,
    eligible066, eligible067, eligible068, eligible069, eligible070, eligible071, eligible072,
    eligible073, eligible074, eligible075, eligible076, eligible077, eligible078, eligible079,
    eligible080, eligible081, eligible082, eligible083, eligible084, eligible085, eligible086,
    eligible087, eligible088, eligible089, eligible090, eligible091, eligible092, Bool.and_self]

/-- The full deduction list reaches the final bit state. -/
theorem all_bit_transitions :
    deductions.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits000 = bits093 := by
  simp only [deductions, List.append_eq]
  rw [List.foldl_append, transition_000]
  rw [List.foldl_append, transition_001]
  rw [List.foldl_append, transition_002]
  rw [List.foldl_append, transition_003]
  rw [List.foldl_append, transition_004]
  rw [List.foldl_append, transition_005]
  rw [List.foldl_append, transition_006]
  rw [List.foldl_append, transition_007]
  rw [List.foldl_append, transition_008]
  rw [List.foldl_append, transition_009]
  rw [List.foldl_append, transition_010]
  rw [List.foldl_append, transition_011]
  rw [List.foldl_append, transition_012]
  rw [List.foldl_append, transition_013]
  rw [List.foldl_append, transition_014]
  rw [List.foldl_append, transition_015]
  rw [List.foldl_append, transition_016]
  rw [List.foldl_append, transition_017]
  rw [List.foldl_append, transition_018]
  rw [List.foldl_append, transition_019]
  rw [List.foldl_append, transition_020]
  rw [List.foldl_append, transition_021]
  rw [List.foldl_append, transition_022]
  rw [List.foldl_append, transition_023]
  rw [List.foldl_append, transition_024]
  rw [List.foldl_append, transition_025]
  rw [List.foldl_append, transition_026]
  rw [List.foldl_append, transition_027]
  rw [List.foldl_append, transition_028]
  rw [List.foldl_append, transition_029]
  rw [List.foldl_append, transition_030]
  rw [List.foldl_append, transition_031]
  rw [List.foldl_append, transition_032]
  rw [List.foldl_append, transition_033]
  rw [List.foldl_append, transition_034]
  rw [List.foldl_append, transition_035]
  rw [List.foldl_append, transition_036]
  rw [List.foldl_append, transition_037]
  rw [List.foldl_append, transition_038]
  rw [List.foldl_append, transition_039]
  rw [List.foldl_append, transition_040]
  rw [List.foldl_append, transition_041]
  rw [List.foldl_append, transition_042]
  rw [List.foldl_append, transition_043]
  rw [List.foldl_append, transition_044]
  rw [List.foldl_append, transition_045]
  rw [List.foldl_append, transition_046]
  rw [List.foldl_append, transition_047]
  rw [List.foldl_append, transition_048]
  rw [List.foldl_append, transition_049]
  rw [List.foldl_append, transition_050]
  rw [List.foldl_append, transition_051]
  rw [List.foldl_append, transition_052]
  rw [List.foldl_append, transition_053]
  rw [List.foldl_append, transition_054]
  rw [List.foldl_append, transition_055]
  rw [List.foldl_append, transition_056]
  rw [List.foldl_append, transition_057]
  rw [List.foldl_append, transition_058]
  rw [List.foldl_append, transition_059]
  rw [List.foldl_append, transition_060]
  rw [List.foldl_append, transition_061]
  rw [List.foldl_append, transition_062]
  rw [List.foldl_append, transition_063]
  rw [List.foldl_append, transition_064]
  rw [List.foldl_append, transition_065]
  rw [List.foldl_append, transition_066]
  rw [List.foldl_append, transition_067]
  rw [List.foldl_append, transition_068]
  rw [List.foldl_append, transition_069]
  rw [List.foldl_append, transition_070]
  rw [List.foldl_append, transition_071]
  rw [List.foldl_append, transition_072]
  rw [List.foldl_append, transition_073]
  rw [List.foldl_append, transition_074]
  rw [List.foldl_append, transition_075]
  rw [List.foldl_append, transition_076]
  rw [List.foldl_append, transition_077]
  rw [List.foldl_append, transition_078]
  rw [List.foldl_append, transition_079]
  rw [List.foldl_append, transition_080]
  rw [List.foldl_append, transition_081]
  rw [List.foldl_append, transition_082]
  rw [List.foldl_append, transition_083]
  rw [List.foldl_append, transition_084]
  rw [List.foldl_append, transition_085]
  rw [List.foldl_append, transition_086]
  rw [List.foldl_append, transition_087]
  rw [List.foldl_append, transition_088]
  rw [List.foldl_append, transition_089]
  rw [List.foldl_append, transition_090]
  rw [List.foldl_append, transition_091]
  exact transition_092

/-- The indexed checker accepts the complete 990-point certificate. -/
theorem checkFast_eq_true : table.checkFast relators subgroupWords deductions = true := by
  have h := bitsAgree_foldl table initial_bits_match deductions
  rw [all_bit_transitions] at h
  unfold TauCeti.CosetTable.checkFast TauCeti.CosetTable.checkActionFast
  change (_ && (deductions.all eligible && _)) = true
  rw [has_root, all_eligible]
  simp only [Bool.true_and]
  apply List.all_eq_true.mpr
  intro t ht
  apply List.all_eq_true.mpr
  intro i hi
  rw [h t i]
  exact final_bits_known t i

/-- The original coset-table checker accepts the same complete certificate. -/
theorem check_eq_true : table.check relators subgroupWords deductions = true := by
  rw [← table.checkFast_eq_check]
  exact checkFast_eq_true

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
