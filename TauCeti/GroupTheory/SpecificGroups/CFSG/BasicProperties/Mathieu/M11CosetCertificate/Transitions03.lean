/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits1
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits2
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions1
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Eligibility
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership00

/-!
# M11 coset deductions: transition group 03

Each block proves word eligibility and a transition between two literal bit states.
The individual computations remain separate so each kernel check covers at most
32 deductions. Their composition is proved in `M11CosetCertificate`.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem eligible024 : deductions024.all eligible = true := by
  simp only [deductions024, List.all_cons, List.all_nil, eligible, r3_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_024 :
    deductions024.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits024 =
      bits025 := by
  decide +kernel

theorem eligible025 : deductions025.all eligible = true := by
  simp only [deductions025, List.all_cons, List.all_nil, eligible, r3_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_025 :
    deductions025.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits025 =
      bits026 := by
  decide +kernel

theorem eligible026 : deductions026.all eligible = true := by
  simp only [deductions026, List.all_cons, List.all_nil, eligible, r3_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_026 :
    deductions026.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits026 =
      bits027 := by
  decide +kernel

theorem eligible027 : deductions027.all eligible = true := by
  simp only [deductions027, List.all_cons, List.all_nil, eligible, r3_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_027 :
    deductions027.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits027 =
      bits028 := by
  decide +kernel

theorem eligible028 : deductions028.all eligible = true := by
  simp only [deductions028, List.all_cons, List.all_nil, eligible, r3_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_028 :
    deductions028.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits028 =
      bits029 := by
  decide +kernel

theorem eligible029 : deductions029.all eligible = true := by
  simp only [deductions029, List.all_cons, List.all_nil, eligible, r3_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_029 :
    deductions029.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits029 =
      bits030 := by
  decide +kernel

theorem eligible030 : deductions030.all eligible = true := by
  simp only [deductions030, List.all_cons, List.all_nil, eligible, r3_mem, r4_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_030 :
    deductions030.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits030 =
      bits031 := by
  decide +kernel

theorem eligible031 : deductions031.all eligible = true := by
  simp only [deductions031, List.all_cons, List.all_nil, eligible, r4_mem, r5_mem, r6_mem,
    r7_mem, r8_mem, r9_mem, r10_mem, r11_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_031 :
    deductions031.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits031 =
      bits032 := by
  decide +kernel

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
